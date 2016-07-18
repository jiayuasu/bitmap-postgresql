/*-------------------------------------------------------------------------
 *
 * bitmaputil.c
 *	  Utility routines for on-disk bitmap index access method.
 *
 * Copyright (c) 2007, PostgreSQL Global Development Group
 * 
 * IDENTIFICATION
 *	  $PostgreSQL$
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"
#include "miscadmin.h"

#include "access/bitmap.h"
#include "access/genam.h"
#include "access/heapam.h"
#include "access/reloptions.h"
#include "storage/bufmgr.h" /* for buffer manager functions */
#include "utils/tqual.h" /* for SnapshotAny */
#include "utils/rel.h" /* for RelationGetDescr */

/*
 * Struct to pass basic vacuum info around
 */
typedef struct bmvacinfo
{
	IndexVacuumInfo *info;
	BMLOVItem lovitem;
} bmvacinfo;

/*
 * What are we vacuuming?
 */
typedef enum bmVacType
{
	BM_VAC_PAGE,
	BM_VAC_LAST_COMPWORD,
	BM_VAC_LAST_WORD
} bmVacType;

/*
 * State structure to store a bunch of useful variables we need to pass
 * around to bitmap vacuum sub routines.
 */
typedef struct bmvacstate
{
	BMLOVItem curlov; /* LOV item for the current vector */ 
	/* variables marking interesting positions in the vector */
	uint64 cur_bitpos; /* the hypothetical location we're at */
	uint64 last_setbit; /* last bit set set as a match */
	uint64 start_reaped;
	uint16 readwordno;	/* current word we're reading */
	uint16 writewordno; /* current word we're writing */

	/* block position at the physical level */
	BlockNumber itr_blk;
	
	Buffer curbuf; /* current buffer we're examining */

	/* actual bitmap pages for old and new */
	BMBitmapVectorPage curbm;
	BMPageOpaque curbmo;

	bool page_updated;	/* have we dirtied the page */

	/* callback info */
	IndexBulkDeleteCallback callback;
	void *callback_state;

	/* overflow storage */
	BMBitmapVectorPageData ovrflw;
	int32 ovrflwwordno;
} bmvacstate;

static void _bitmap_findnextword(BMBatchWords* words, uint32 nextReadNo);
static void _bitmap_resetWord(BMBatchWords *words, uint32 prevStartNo);
static uint8 _bitmap_find_bitset(BM_WORD word, uint8 lastPos);
static void vacuum_vector(bmvacinfo vacinfo, IndexBulkDeleteCallback callback,
			              void *callback_state);
static void fill_reaped(bmvacstate *state, uint64 start, uint64 end);
static void vacuum_fill_word(bmvacstate *state, bmVacType vactype);
static void vacuum_literal_word(bmvacstate *state, bmVacType vavtype);
static void try_shrink_bitmap(bmvacstate *state);
static void progress_write_pos(bmvacstate *state);
static void vacuum_last_words(bmvacstate *state);
static BM_WORD vactype_get_word(bmvacstate *state, bmVacType type);
static void put_vacuumed_literal_word(bmvacstate *state, bmVacType type,
									  BM_WORD word);
static void vacuum_append_ovrflw_words(bmvacstate *state);

/*
 * _bitmap_formitem() -- construct a LOV entry.
 *
 * If the given tid number is greater than BM_WORD_SIZE, we
 * construct the first fill word for this bitmap vector.
 */
BMLOVItem
_bitmap_formitem(uint64 currTidNumber)
{
    /* Allocate a new LOV item */
    BMLOVItem bmitem = (BMLOVItem)palloc(BM_LOV_ITEM_SIZE);

#ifdef DEBUG_BMI
	  elog(NOTICE,"[_bitmap_formitem] BEGIN"
	       "\n\tcurrTidNumber = %llu"
	       ,currTidNumber
	       );
#endif

    /* Initialise the LOV structure */
    bmitem->bm_lov_head = bmitem->bm_lov_tail = InvalidBlockNumber;
    bmitem->bm_last_setbit = 0;
    bmitem->bm_last_compword = LITERAL_ALL_ONE;
    bmitem->bm_last_word = LITERAL_ALL_ZERO;
    bmitem->lov_words_header = BM_LOV_WORDS_NO_FILL;
    bmitem->bm_last_tid_location = 0;

    /* fill up all existing bits with 0. */
    if (currTidNumber > BM_WORD_SIZE)
    {
	uint32		numOfTotalFillWords;
	BM_WORD	numOfFillWords;

	numOfTotalFillWords = (currTidNumber-1)/BM_WORD_SIZE;

	numOfFillWords = (numOfTotalFillWords >= MAX_FILL_LENGTH) ? 
	MAX_FILL_LENGTH : numOfTotalFillWords;

	bmitem->bm_last_compword = BM_MAKE_FILL_WORD(0, numOfFillWords);
	bmitem->bm_last_word = LITERAL_ALL_ZERO;
	bmitem->lov_words_header = BM_LAST_COMPWORD_BIT;
	bmitem->bm_last_tid_location = numOfFillWords * BM_WORD_SIZE;

	/*
	* If all zeros are too many to fit in one word, then
	* we set bm_last_setbit so that the remaining zeros can
	* be handled outside.
	*/
	if (numOfTotalFillWords > numOfFillWords)
	    bmitem->bm_last_setbit = numOfFillWords*BM_WORD_SIZE;
    }

#ifdef DEBUG_BMI
    elog(NOTICE,"[_bitmap_formitem] END");
#endif
    return bmitem;
}

/*
 * _bitmap_init_batchwords() -- initialize a BMBatchWords in a given
 * memory context.
 *
 * Allocate spaces for bitmap header words and bitmap content words.
 */
void
_bitmap_init_batchwords(BMBatchWords* words,
						uint32 maxNumOfWords,
						MemoryContext mcxt)
{
	uint32	numOfHeaderWords;
	MemoryContext oldcxt;

	words->nwordsread = 0;
	words->nextread = 1;
	words->startNo = 0;
	words->nwords = 0;

	numOfHeaderWords = BM_CALC_H_WORDS(maxNumOfWords);

	words->maxNumOfWords = maxNumOfWords;

	/* Make sure that we have at least one page of words */
	Assert(words->maxNumOfWords >= BM_NUM_OF_HRL_WORDS_PER_PAGE);

	oldcxt = MemoryContextSwitchTo(mcxt);
	words->hwords = palloc0(sizeof(BM_WORD)*numOfHeaderWords);
	words->cwords = palloc0(sizeof(BM_WORD)*words->maxNumOfWords);
	MemoryContextSwitchTo(oldcxt);
}

/*
 * _bitmap_copy_batchwords() -- copy a given BMBatchWords to another
 *	BMBatchWords.
 */
void
_bitmap_copy_batchwords(BMBatchWords* words, BMBatchWords* copyWords)
{
	uint32	numOfHeaderWords;

	copyWords->maxNumOfWords = words->maxNumOfWords;
	copyWords->nwordsread = words->nwordsread;
	copyWords->nextread = words->nextread;
	copyWords->firstTid = words->firstTid;
	copyWords->startNo = words->startNo;
	copyWords->nwords = words->nwords;

	numOfHeaderWords = BM_CALC_H_WORDS(copyWords->maxNumOfWords);

	memcpy(copyWords->hwords, words->hwords,
			sizeof(BM_WORD)*numOfHeaderWords);
	memcpy(copyWords->cwords, words->cwords,
			sizeof(BM_WORD)*copyWords->maxNumOfWords);
}

/*
 * _bitmap_reset_batchwords() -- reset the BMBatchWords for re-use.
 */
void
_bitmap_reset_batchwords(BMBatchWords *words)
{
	words->startNo = 0;
	words->nwords = 0;
	MemSet(words->hwords, 0,
		   sizeof(BM_WORD) * BM_CALC_H_WORDS(words->maxNumOfWords));
}

/*
 * _bitmap_cleanup_batchwords() -- release spaces allocated for the BMBatchWords.
 */
void _bitmap_cleanup_batchwords(BMBatchWords* words)
{
	if (words == NULL)
		return;

	if (words->hwords)
		pfree(words->hwords);
	if (words->cwords)
		pfree(words->cwords);
}

/*
 * _bitmap_cleanup_scanpos() -- release space allocated for
 * 	BMVector.
 */
void
_bitmap_cleanup_scanpos(BMVector bmScanPos, uint32 numBitmapVectors)
{
	uint32 keyNo;

	if (numBitmapVectors == 0)
		return;
		
	for (keyNo=0; keyNo<numBitmapVectors; keyNo++)
	{
		if (BufferIsValid((bmScanPos[keyNo]).bm_lovBuffer))
		{
			ReleaseBuffer((bmScanPos[keyNo]).bm_lovBuffer);
		}
			

		_bitmap_cleanup_batchwords((bmScanPos[keyNo]).bm_batchWords);
		if (bmScanPos[keyNo].bm_batchWords != NULL)
			pfree((bmScanPos[keyNo]).bm_batchWords);
	}

	pfree(bmScanPos);
}

/*
 * _bitmap_findnexttid() -- find the next tid location in a given batch
 *  of bitmap words.
 */
uint64
_bitmap_findnexttid(BMBatchWords *words, BMIterateResult *result)
{
	/*
	 * If there is not tids from previous computation, then we
	 * try to find next set of tids.
	 */

	if (result->nextTidLoc >= result->numOfTids)
		_bitmap_findnexttids(words, result, BM_BATCH_TIDS);

	/* if find more tids, then return the first one */
	if (result->nextTidLoc < result->numOfTids)
	{
		result->nextTidLoc++;
		return (result->nextTids[result->nextTidLoc-1]);
	}

	/* no more tids */
	return 0;
}

/*
 * _bitmap_findprevtid() -- find the previous tid location in an array of tids.
 */
void
_bitmap_findprevtid(BMIterateResult *result)
{
	Assert(result->nextTidLoc > 0);
	result->nextTidLoc--;
}

/*
 * _bitmap_findnexttids() -- find the next set of tids from a given
 *  batch of bitmap words.
 *
 * The maximum number of tids to be found is defined in 'maxTids'.
 */
void
_bitmap_findnexttids(BMBatchWords *words, BMIterateResult *result,
					 uint32 maxTids)
{
	bool done = false;

	result->nextTidLoc = result->numOfTids = 0;
	while (words->nwords > 0 && result->numOfTids < maxTids && !done)
	{
		uint8 oldScanPos = result->lastScanPos;
		BM_WORD word = words->cwords[result->lastScanWordNo];

		/* new word, zero filled */
		if (oldScanPos == 0 &&
			((IS_FILL_WORD(words->hwords, result->lastScanWordNo) && 
			  GET_FILL_BIT(word) == 0) || word == 0))
		{
			uint32	fillLength;
			if (word == 0)
				fillLength = 1;
			else
				fillLength = FILL_LENGTH(word);

			/* skip over non-matches */
			result->nextTid += fillLength * BM_WORD_SIZE;
			result->lastScanWordNo++;
			words->nwords--;
			result->lastScanPos = 0;
			continue;
		}
		else if (IS_FILL_WORD(words->hwords, result->lastScanWordNo)
				 && GET_FILL_BIT(word) == 1)
		{
			uint32	nfillwords = FILL_LENGTH(word);
			uint8 	bitNo;

			while (result->numOfTids + BM_WORD_SIZE <= maxTids &&
				   nfillwords > 0)
			{
				/* explain the fill word */
				for (bitNo = 0; bitNo < BM_WORD_SIZE; bitNo++)
					result->nextTids[result->numOfTids++] = ++result->nextTid;

				nfillwords--;
				/* update fill word to reflect expansion */
				words->cwords[result->lastScanWordNo]--;
			}

			if (nfillwords == 0)
			{
				result->lastScanWordNo++;
				words->nwords--;
				result->lastScanPos = 0;
				continue;
			}
			else
			{
				done = true;
				break;
			}
		}
		else
		{
			if(oldScanPos == 0)
				oldScanPos = BM_WORD_SIZE + 1;

			while (oldScanPos != 0 && result->numOfTids < maxTids)
			{
				BM_WORD		w;

				if (oldScanPos == BM_WORD_SIZE + 1)
					oldScanPos = 0;

				w = words->cwords[result->lastScanWordNo];
				result->lastScanPos = _bitmap_find_bitset(w, oldScanPos);

				/* did we fine a bit set in this word? */
				if (result->lastScanPos != 0)
				{
					result->nextTid += (result->lastScanPos - oldScanPos);
					result->nextTids[result->numOfTids++] = result->nextTid;
				}
				else
				{
					result->nextTid += BM_WORD_SIZE - oldScanPos;
					/* start scanning a new word */
					words->nwords--;
					result->lastScanWordNo++;
					result->lastScanPos = 0;
				}
				oldScanPos = result->lastScanPos;
			}
		}
	}
}

/*
 * _bitmap_intesect() is dead code because streaming intersects
 * PagetableEntry structures, not raw batch words. It's possible we may
 * want to intersect batches later though -- it would definately improve
 * streaming of intersections.
 */

#ifdef NOT_USED

/*
 * _bitmap_intersect() -- intersect 'numBatches' bitmap words.
 *
 * All 'numBatches' bitmap words are HRL compressed. The result
 * bitmap words HRL compressed, except that fill set words(1s) may
 * be lossily compressed.
 */
void
_bitmap_intersect(BMBatchWords **batches, uint32 numBatches,
				  BMBatchWords *result)
{
	bool done = false;
	uint32	*prevStartNos;
	uint32	nextReadNo;
	uint32	batchNo;

	Assert(numBatches > 0);

	prevStartNos = (uint32 *)palloc0(numBatches * sizeof(uint32));
	nextReadNo = batches[0]->nextread;

	while (!done &&	result->nwords < result->maxNumOfWords)
	{
		BM_WORD andWord = LITERAL_ALL_ONE;
		BM_WORD	word;

		bool		andWordIsLiteral = true;

		/*
    	 * We walk through the bitmap word in each list one by one
         * without de-compress the bitmap words. 'nextReadNo' defines
         * the position of the next word that should be read in an
         * uncompressed format.
         */
		for (batchNo = 0; batchNo < numBatches; batchNo++)
		{
			uint32 offs;
			BMBatchWords *bch = batches[batchNo];

			/* skip nextReadNo - nwordsread - 1 words */
			_bitmap_findnextword(bch, nextReadNo);

			if (bch->nwords == 0)
			{
				done = true;
				break;
			}

			Assert(bch->nwordsread == nextReadNo - 1);

			/* Here, startNo should point to the word to be read. */
			offs = bch->startNo;
			word = bch->cwords[offs];

			if (CUR_WORD_IS_FILL(bch) && (GET_FILL_BIT(word) == 0))
			{
				uint32		n;
				
				bch->nwordsread += FILL_LENGTH(word);

				n = bch->nwordsread - nextReadNo + 1;
				andWord = BM_MAKE_FILL_WORD(0, n);
				andWordIsLiteral = false;

				nextReadNo = bch->nwordsread + 1;
				bch->startNo++;
				bch->nwords--;
				break;
			}
			else if (CUR_WORD_IS_FILL(bch) && (GET_FILL_BIT(word) == 1))
			{
				bch->nwordsread++;

				prevStartNos[batchNo] = bch->startNo;

				if (FILL_LENGTH(word) == 1)
				{
					bch->startNo++;
					bch->nwords--;
				}
				else
				{
					uint32 s = bch->startNo;
					bch->cwords[s]--;
				}
				andWordIsLiteral = true;
			}
			else if (!CUR_WORD_IS_FILL(bch))
			{
				prevStartNos[batchNo] = bch->startNo;

				andWord &= word;
				bch->nwordsread++;
				bch->startNo++;
				bch->nwords--;
				andWordIsLiteral = true;
			}
		}

		/* Since there are not enough words in this attribute break this loop */
		if (done)
		{
			uint32 preBatchNo;

			/* reset the attributes before batchNo */
			for (preBatchNo = 0; preBatchNo < batchNo; preBatchNo++)
			{
				_bitmap_resetWord(batches[preBatchNo], prevStartNos[preBatchNo]);
			}
			break;
		}
		else
		{
			if (!andWordIsLiteral)
			{
				uint32	off = result->nwords/BM_WORD_SIZE;
				uint32	w = result->nwords;

				result->hwords[off] |= WORDNO_GET_HEADER_BIT(w);
			}
			result->cwords[result->nwords] = andWord;
			result->nwords++;
		}

		if (andWordIsLiteral)
			nextReadNo++;

		if (batchNo == 1 && bch->nwords == 0)
			done = true;
	}

	/* set the nextReadNo */
	for (batchNo = 0; batchNo < numBatches; batchNo++)
		batches[batchNo]->nextread = nextReadNo;

	pfree(prevStartNos);
}

#endif /* NOT_USED */

/*
 * _bitmap_union() -- union 'numBatches' bitmaps
 *
 * All bitmap words are HRL compressed. The result bitmap words are also
 * HRL compressed, except that fill unset words may be lossily compressed.
 */
void
_bitmap_union(BMBatchWords **batches, uint32 numBatches, BMBatchWords *result)
{
	bool 		done = false;
	uint32 	   *prevstarts;
	uint32		nextReadNo;
	uint32		batchNo;

	Assert (numBatches >= 0);

	if (numBatches == 0)
		return;

	/* save batch->startNo for each input bitmap vector */
	prevstarts = (uint32 *)palloc0(numBatches * sizeof(uint32));

	/* 
	 * Each batch should have the same next read offset, so take 
	 * the first one
	 */
	nextReadNo = batches[0]->nextread;

	while (!done &&	result->nwords < result->maxNumOfWords)
	{
		BM_WORD orWord = LITERAL_ALL_ZERO;
		BM_WORD	word;
		bool		orWordIsLiteral = true;

		for (batchNo = 0; batchNo < numBatches; batchNo++)
		{
			BMBatchWords *bch = batches[batchNo];

			/* skip nextReadNo - nwordsread - 1 words */
			_bitmap_findnextword(bch, nextReadNo);

			if (bch->nwords == 0)
			{
				done = true;
				break;
			}

			Assert(bch->nwordsread == nextReadNo - 1);

			/* Here, startNo should point to the word to be read. */
			word = bch->cwords[bch->startNo];

			if (CUR_WORD_IS_FILL(bch) && GET_FILL_BIT(word) == 1)
			{
				/* Fill word represents matches */
				bch->nwordsread += FILL_LENGTH(word);
				orWord = BM_MAKE_FILL_WORD(1, bch->nwordsread - nextReadNo + 1);
				orWordIsLiteral = false;

				nextReadNo = bch->nwordsread + 1;
				bch->startNo++;
				bch->nwords--;
				break;
			}
			else if (CUR_WORD_IS_FILL(bch) && GET_FILL_BIT(word) == 0)
			{
				/* Fill word represents no matches */

				bch->nwordsread++;
				prevstarts[batchNo] = bch->startNo;
				if (FILL_LENGTH(word) == 1)
				{
					bch->startNo++;
					bch->nwords--;
				}
				else
					bch->cwords[bch->startNo]--;
				orWordIsLiteral = true;
			}
			else if (!CUR_WORD_IS_FILL(bch))
			{
				/* word is literal */
				prevstarts[batchNo] = bch->startNo;
				orWord |= word;
				bch->nwordsread++;
				bch->startNo++;
				bch->nwords--;
				orWordIsLiteral = true;
			}
		}

		if (done)
		{
			uint32 i;

			/* reset the attributes before batchNo */
			for (i = 0; i < batchNo; i++)
				_bitmap_resetWord(batches[i], prevstarts[i]);
			break;
		}
		else
		{
			if (!orWordIsLiteral)
			{
				 /* Word is not literal, update the result header */
				uint32 	offs = result->nwords/BM_WORD_SIZE;
				uint32	n = result->nwords;
				result->hwords[offs] |= WORDNO_GET_HEADER_BIT(n);
			}
			result->cwords[result->nwords] = orWord;
			result->nwords++;
		}

		if (orWordIsLiteral)
			nextReadNo++;

		/* we just processed the last batch and it was empty */
		if (batchNo == numBatches - 1 && batches[batchNo]->nwords == 0)
			done = true;
	}

	/* set the next word to read for all input vectors */
	for (batchNo = 0; batchNo < numBatches; batchNo++)
		batches[batchNo]->nextread = nextReadNo;

	pfree(prevstarts);
}

/*
 * _bitmap_findnextword() -- Find the next word whose position is
 *        	                'nextReadNo' in an uncompressed format.
 */
static void
_bitmap_findnextword(BMBatchWords *words, uint32 nextReadNo)
{
	/* 
     * 'words->nwordsread' defines how many un-compressed words
     * have been read in this bitmap. We read from
     * position 'startNo', and increment 'words->nwordsread'
     * differently based on the type of words that are read, until
     * 'words->nwordsread' is equal to 'nextReadNo'.
     */
	while (words->nwords > 0 && words->nwordsread < nextReadNo - 1)
	{
		/* Get the current word */
		BM_WORD word = words->cwords[words->startNo];

		if (CUR_WORD_IS_FILL(words))
		{
			if(FILL_LENGTH(word) <= (nextReadNo - words->nwordsread - 1))
			{
				words->nwordsread += FILL_LENGTH(word);
				words->startNo++;
				words->nwords--;
			}
			else
			{
				words->cwords[words->startNo] -= (nextReadNo - words->nwordsread - 1);
				words->nwordsread = nextReadNo - 1;
			}
		}
		else
		{
			words->nwordsread++;
			words->startNo++;
			words->nwords--;
		}
	}
}

/*
 * _bitmap_resetWord() -- Reset the read position in an BMBatchWords
 *       	              to its previous value.
 *
 * Reset the read position in an BMBatchWords to its previous value,
 * which is given in 'prevStartNo'. Based on different type of words read,
 * the actual bitmap word may need to be changed.
 */
static void
_bitmap_resetWord(BMBatchWords *words, uint32 prevStartNo)
{
	if (words->startNo > prevStartNo)
	{
		Assert(words->startNo == prevStartNo + 1);
		words->startNo = prevStartNo;
		words->nwords++;
	}
	else
	{
		Assert(words->startNo == prevStartNo);
		Assert(CUR_WORD_IS_FILL(words));
		words->cwords[words->startNo]++;
	}
	words->nwordsread--;
}


/*
 * _bitmap_find_bitset() -- find the rightmost set bit (bit=1) in the 
 * 		given word since 'lastPos', not including 'lastPos'.
 *
 * The rightmost bit in the given word is considered the position 1, and
 * the leftmost bit is considered the position BM_WORD_SIZE.
 *
 * If such set bit does not exist in this word, 0 is returned.
 */
static uint8
_bitmap_find_bitset(BM_WORD word, uint8 lastPos)
{
	uint8 pos = lastPos + 1;
	BM_WORD	rightmostBitWord;

	if (pos > BM_WORD_SIZE)
	  return 0;

	rightmostBitWord = (((BM_WORD)1) << (pos-1));

	while (pos <= BM_WORD_SIZE && (word & rightmostBitWord) == 0)
	{
		rightmostBitWord <<= 1;
		pos++;
	}

	if (pos > BM_WORD_SIZE)
		pos = 0;

	return pos;
}

/*
 * _bitmap_begin_iterate() -- initialize the given BMIterateResult instance.
 */
void
_bitmap_begin_iterate(BMBatchWords *words, BMIterateResult *result)
{
	result->nextTid = words->firstTid;
	result->lastScanPos = 0;
	result->lastScanWordNo = words->startNo;
	result->numOfTids = 0;
	result->nextTidLoc = 0;
}


/*
 * _bitmap_log_newpage() -- log a new page.
 *
 * This function is called before writing a new buffer.
 */
void
_bitmap_log_newpage(Relation rel, uint8 info, Buffer buf)
{
	Page page;

	xl_bm_newpage		xlNewPage;
	XLogRecPtr			recptr;
	XLogRecData			rdata[1];

	page = BufferGetPage(buf);

	xlNewPage.bm_node = rel->rd_node;
	xlNewPage.bm_new_blkno = BufferGetBlockNumber(buf);

	rdata[0].buffer = InvalidBuffer;
	rdata[0].data = (char *)&xlNewPage;
	rdata[0].len = sizeof(xl_bm_newpage);
	rdata[0].next = NULL;
			
	recptr = XLogInsert(RM_BITMAP_ID, info, rdata);

	PageSetLSN(page, recptr);
	PageSetTLI(page, ThisTimeLineID);
}

/*
 * _bitmap_log_metapage() -- log the changes to the metapage
 */
void
_bitmap_log_metapage(Relation rel, Page page)
{
	BMMetaPage metapage = (BMMetaPage) PageGetContents(page);

	xl_bm_metapage*		xlMeta;
	XLogRecPtr			recptr;
	XLogRecData			rdata[1];

	xlMeta = (xl_bm_metapage *)
		palloc(MAXALIGN(sizeof(xl_bm_metapage)));
	xlMeta->bm_node = rel->rd_node;
	xlMeta->bm_lov_heapId = metapage->bm_lov_heapId;
	xlMeta->bm_lov_indexId = metapage->bm_lov_indexId;
	xlMeta->bm_lov_lastpage = metapage->bm_lov_lastpage;

	rdata[0].buffer = InvalidBuffer;
	rdata[0].data = (char*)xlMeta;
	rdata[0].len = MAXALIGN(sizeof(xl_bm_metapage));
	rdata[0].next = NULL;
			
	recptr = XLogInsert(RM_BITMAP_ID, XLOG_BITMAP_INSERT_META, rdata);

	PageSetLSN(page, recptr);
	PageSetTLI(page, ThisTimeLineID);
	pfree(xlMeta);
}

/*
 * _bitmap_log_bitmap_lastwords() -- log the last two words in a bitmap.
 */
void
_bitmap_log_bitmap_lastwords(Relation rel, Buffer lovBuffer, 
							 OffsetNumber lovOffset, BMLOVItem lovItem)
{
	xl_bm_bitmap_lastwords	xlLastwords;
	XLogRecPtr				recptr;
	XLogRecData				rdata[1];

	xlLastwords.bm_node = rel->rd_node;
	xlLastwords.bm_last_compword = lovItem->bm_last_compword;
	xlLastwords.bm_last_word = lovItem->bm_last_word;
	xlLastwords.lov_words_header = lovItem->lov_words_header;
	xlLastwords.bm_lov_blkno = BufferGetBlockNumber(lovBuffer);
	xlLastwords.bm_lov_offset = lovOffset;

	rdata[0].buffer = InvalidBuffer;
	rdata[0].data = (char*)&xlLastwords;
	rdata[0].len = sizeof(xl_bm_bitmap_lastwords);
	rdata[0].next = NULL;

	recptr = XLogInsert(RM_BITMAP_ID, XLOG_BITMAP_INSERT_BITMAP_LASTWORDS, 
						rdata);

	PageSetLSN(BufferGetPage(lovBuffer), recptr);
	PageSetTLI(BufferGetPage(lovBuffer), ThisTimeLineID);
}

/*
 * _bitmap_log_lovitem() -- log adding a new lov item to a lov page.
 */
void
_bitmap_log_lovitem(Relation rel, Buffer lovBuffer, OffsetNumber offset,
					BMLOVItem lovItem, Buffer metabuf, bool is_new_lov_blkno)
{
	Page lovPage = BufferGetPage(lovBuffer);

	xl_bm_lovitem	xlLovItem;
	XLogRecPtr		recptr;
	XLogRecData		rdata[1];

	xlLovItem.bm_node = rel->rd_node;
	xlLovItem.bm_lov_blkno = BufferGetBlockNumber(lovBuffer);
	xlLovItem.bm_lov_offset = offset;
	memcpy(&(xlLovItem.bm_lovItem), lovItem, sizeof(BMLOVItemData));
	xlLovItem.bm_is_new_lov_blkno = is_new_lov_blkno;

	rdata[0].buffer = InvalidBuffer;
	rdata[0].data = (char*)&xlLovItem;
	rdata[0].len = sizeof(xl_bm_lovitem);
	rdata[0].next = NULL;

	recptr = XLogInsert(RM_BITMAP_ID, 
						XLOG_BITMAP_INSERT_LOVITEM, rdata);

	if (is_new_lov_blkno)
	{
		Page metapage = BufferGetPage(metabuf);

		PageSetLSN(metapage, recptr);
		PageSetTLI(metapage, ThisTimeLineID);
	}

	PageSetLSN(lovPage, recptr);
	PageSetTLI(lovPage, ThisTimeLineID);
}

/*
 * _bitmap_log_bitmapwords() -- log new bitmap words to be inserted.
 */
void
_bitmap_log_bitmapwords(Relation rel, Buffer bitmapBuffer, Buffer lovBuffer,
						OffsetNumber lovOffset, BMTIDBuffer* buf,
						uint64 words_written, uint64 tidnum,
						BlockNumber nextBlkno,
						bool isLast, bool isFirst)
{
	Page				bitmapPage;
	BMPageOpaque		bitmapPageOpaque;
	xl_bm_bitmapwords  *xlBitmapWords;
	XLogRecPtr			recptr;
	XLogRecData			rdata[1];
	uint64*				lastTids;
	BM_WORD*		cwords;
	BM_WORD*		hwords;
	int					lastTids_size;
	int					cwords_size;
	int					hwords_size;
	Page lovPage = BufferGetPage(lovBuffer);

	lastTids_size = buf->curword * sizeof(uint64);
	cwords_size = buf->curword * sizeof(BM_WORD);
	hwords_size = (BM_CALC_H_WORDS(buf->curword)) *
					sizeof(BM_WORD);

	bitmapPage = BufferGetPage(bitmapBuffer);
	bitmapPageOpaque =
		(BMPageOpaque)PageGetSpecialPointer(bitmapPage);

	xlBitmapWords = (xl_bm_bitmapwords *)
		palloc0(sizeof(xl_bm_bitmapwords) + lastTids_size +
				cwords_size + hwords_size);

	xlBitmapWords->bm_node = rel->rd_node;
	xlBitmapWords->bm_blkno = BufferGetBlockNumber(bitmapBuffer);
	xlBitmapWords->bm_next_blkno = nextBlkno;
	xlBitmapWords->bm_last_tid = bitmapPageOpaque->bm_last_tid_location;
	xlBitmapWords->bm_lov_blkno = BufferGetBlockNumber(lovBuffer);
	xlBitmapWords->bm_lov_offset = lovOffset;
	xlBitmapWords->bm_last_compword = buf->last_compword;
	xlBitmapWords->bm_last_word = buf->last_word;
	xlBitmapWords->lov_words_header = 
		(buf->is_last_compword_fill) ? 
		BM_LAST_COMPWORD_BIT : BM_LOV_WORDS_NO_FILL;
	xlBitmapWords->bm_last_setbit = tidnum;
	xlBitmapWords->bm_is_last = isLast;
	xlBitmapWords->bm_is_first = isFirst;

	xlBitmapWords->bm_start_wordno = buf->start_wordno;
	xlBitmapWords->bm_words_written = words_written;
	xlBitmapWords->bm_num_cwords = buf->curword;
	lastTids = (uint64*)(((char*)xlBitmapWords) +
						 sizeof(xl_bm_bitmapwords));
	memcpy(lastTids, buf->last_tids,
		   buf->curword * sizeof(uint64));

	cwords = (BM_WORD*)(((char*)xlBitmapWords) +
						 sizeof(xl_bm_bitmapwords) + lastTids_size);
	memcpy(cwords, buf->cwords, cwords_size);
	hwords = (BM_WORD*)(((char*)xlBitmapWords) +
						 sizeof(xl_bm_bitmapwords) + lastTids_size +
						 cwords_size);
	memcpy(hwords, buf->hwords, hwords_size);

	rdata[0].buffer = InvalidBuffer;
	rdata[0].data = (char*)xlBitmapWords;
	rdata[0].len = sizeof(xl_bm_bitmapwords) + lastTids_size +
					cwords_size + hwords_size;
	rdata[0].next = NULL;

	recptr = XLogInsert(RM_BITMAP_ID, XLOG_BITMAP_INSERT_WORDS, rdata);

	PageSetLSN(bitmapPage, recptr);
	PageSetTLI(bitmapPage, ThisTimeLineID);

	PageSetLSN(lovPage, recptr);
	PageSetTLI(lovPage, ThisTimeLineID);

	pfree(xlBitmapWords);
}

/*
 * _bitmap_log_updateword() -- log updating a single word in a given
 * 	bitmap page.
 */
void
_bitmap_log_updateword(Relation rel, Buffer bitmapBuffer, int word_no)
{
	Page				bitmapPage;
	BMBitmapVectorPage			bitmap;
	xl_bm_updateword	xlBitmapWord;
	XLogRecPtr			recptr;
	XLogRecData			rdata[1];

	bitmapPage = BufferGetPage(bitmapBuffer);
	bitmap = (BMBitmapVectorPage) PageGetContents(bitmapPage);

	xlBitmapWord.bm_node = rel->rd_node;
	xlBitmapWord.bm_blkno = BufferGetBlockNumber(bitmapBuffer);
	xlBitmapWord.bm_word_no = word_no;
	xlBitmapWord.bm_cword = bitmap->cwords[word_no];
	xlBitmapWord.bm_hword = bitmap->hwords[word_no/BM_WORD_SIZE];

	rdata[0].buffer = InvalidBuffer;
	rdata[0].data = (char*)&xlBitmapWord;
	rdata[0].len = sizeof(xl_bm_updateword);
	rdata[0].next = NULL;

	recptr = XLogInsert(RM_BITMAP_ID, XLOG_BITMAP_UPDATEWORD, rdata);

	PageSetLSN(bitmapPage, recptr);
	PageSetTLI(bitmapPage, ThisTimeLineID);
}
						

/*
 * _bitmap_log_updatewords() -- log updating bitmap words in one or
 * 	two bitmap pages.
 *
 * If nextBuffer is Invalid, we only update one page.
 *
 */
void
_bitmap_log_updatewords(Relation rel,
						Buffer lovBuffer, OffsetNumber lovOffset,
						Buffer firstBuffer, Buffer secondBuffer,
						bool new_lastpage)
{
	Page				firstPage = NULL;
	Page				secondPage = NULL;
	BMBitmapVectorPage			firstBitmap;
	BMBitmapVectorPage			secondBitmap;
	BMPageOpaque		firstOpaque;
	BMPageOpaque		secondOpaque;

	xl_bm_updatewords	xlBitmapWords;
	XLogRecPtr			recptr;
	XLogRecData			rdata[1];


	firstPage = BufferGetPage(firstBuffer);
	firstBitmap = (BMBitmapVectorPage) PageGetContents(firstPage);
	firstOpaque = (BMPageOpaque)PageGetSpecialPointer(firstPage);
	xlBitmapWords.bm_two_pages = false;
	xlBitmapWords.bm_first_blkno = BufferGetBlockNumber(firstBuffer);
	memcpy(&xlBitmapWords.bm_first_cwords,
			firstBitmap->cwords,
			BM_NUM_OF_HRL_WORDS_PER_PAGE * sizeof(BM_WORD));
	memcpy(&xlBitmapWords.bm_first_hwords,
			firstBitmap->hwords,
			BM_NUM_OF_HEADER_WORDS * sizeof(BM_WORD));
	xlBitmapWords.bm_first_last_tid = firstOpaque->bm_last_tid_location;
	xlBitmapWords.bm_first_num_cwords =
		firstOpaque->bm_hrl_words_used;
	xlBitmapWords.bm_next_blkno = firstOpaque->bm_bitmap_next;

	if (BufferIsValid(secondBuffer))
	{
		secondPage = BufferGetPage(secondBuffer);
		secondBitmap = (BMBitmapVectorPage) PageGetContents(secondPage);
		secondOpaque = (BMPageOpaque)PageGetSpecialPointer(secondPage);

		xlBitmapWords.bm_two_pages = true;
		xlBitmapWords.bm_second_blkno = BufferGetBlockNumber(secondBuffer);

		memcpy(&xlBitmapWords.bm_second_cwords,
				secondBitmap->cwords,
				BM_NUM_OF_HRL_WORDS_PER_PAGE * sizeof(BM_WORD));
		memcpy(&xlBitmapWords.bm_second_hwords,
				secondBitmap->hwords,
				BM_NUM_OF_HEADER_WORDS * sizeof(BM_WORD));
		xlBitmapWords.bm_second_last_tid = secondOpaque->bm_last_tid_location;
		xlBitmapWords.bm_second_num_cwords =
			secondOpaque->bm_hrl_words_used;
		xlBitmapWords.bm_next_blkno = secondOpaque->bm_bitmap_next;
	}

	xlBitmapWords.bm_node = rel->rd_node;

	rdata[0].buffer = InvalidBuffer;
	rdata[0].data = (char*)&xlBitmapWords;
	rdata[0].len = sizeof(xl_bm_updatewords);
	rdata[0].next = NULL;

	recptr = XLogInsert(RM_BITMAP_ID, XLOG_BITMAP_UPDATEWORDS, rdata);

	PageSetLSN(firstPage, recptr);
	PageSetTLI(firstPage, ThisTimeLineID);

	if (BufferIsValid(secondBuffer))
	{
		PageSetLSN(secondPage, recptr);
		PageSetTLI(secondPage, ThisTimeLineID);
	}

	if (new_lastpage)
	{
		Page lovPage = BufferGetPage(lovBuffer);

		PageSetLSN(lovPage, recptr);
		PageSetTLI(lovPage, ThisTimeLineID);
	}
}

Datum
bmoptions(PG_FUNCTION_ARGS)
{
	Datum		reloptions = PG_GETARG_DATUM(0);
	bool		validate = PG_GETARG_BOOL(1);
	bytea	   *result;

	/*
	 * It's not clear that fillfactor is useful for on-disk bitmap index,
	 * but for the moment we'll accept it anyway.  (It won't do anything...)
	 */
#define BM_MIN_FILLFACTOR			10
#define BM_DEFAULT_FILLFACTOR		100

	result = default_reloptions(reloptions, validate,
								BM_MIN_FILLFACTOR,
								BM_DEFAULT_FILLFACTOR);
	if (result)
		PG_RETURN_BYTEA_P(result);
	PG_RETURN_NULL();
}

/*
 * Vacuum tuples out of a bitmap index.
 */

void
_bitmap_vacuum(IndexVacuumInfo *info, IndexBulkDeleteResult *stats,
			   IndexBulkDeleteCallback callback, void *callback_state)
{
	Buffer metabuf;
	BMMetaPage metapage;
	Relation index = info->index;
	bmvacinfo vacinfo;
	HeapScanDesc scan;
	Relation lovheap;
	HeapTuple tuple;

	vacinfo.info = info;

	metabuf = _bitmap_getbuf(info->index, BM_METAPAGE, BM_READ);
	metapage = (BMMetaPage)PageGetContents(BufferGetPage(metabuf)); 

	lovheap = heap_open(metapage->bm_lov_heapId, AccessShareLock);
	scan = heap_beginscan(lovheap, SnapshotAny, 0, NULL);

	while ((tuple = heap_getnext(scan, ForwardScanDirection)))
	{
		BMLOVItem 		lovitem;
		BlockNumber 	lov_block;
		OffsetNumber 	lov_off;
		TupleDesc   	desc;
        Datum       	d;
		bool			isnull;
		Buffer			lov_buf;
		Page			page;

        desc = RelationGetDescr(lovheap);

        d = heap_getattr(tuple, desc->natts - 1, desc, &isnull);
		Assert(!isnull);
        lov_block = DatumGetInt32(d);
		
        d = heap_getattr(tuple, desc->natts - 0, desc, &isnull);
		Assert(!isnull);
        lov_off = DatumGetInt16(d);

		lov_buf = _bitmap_getbuf(index, lov_block, BM_READ);
		page = BufferGetPage(lov_buf);
		lovitem = (BMLOVItem)PageGetItem(page,
										 PageGetItemId(page,lov_off));
		vacinfo.lovitem = lovitem;

#ifdef DEBUG_BMI
		elog(NOTICE, "---- start vac");
		elog(NOTICE, "value = %i", (int)heap_getattr(tuple, 1, desc, &isnull));
#endif
		vacuum_vector(vacinfo, callback, callback_state);
		_bitmap_relbuf(lov_buf);
	}
	
	/* XXX: be careful to vacuum NULL vector */
	
	/*vacuum null vector */

	/* iterate over all vectors, call for each */

	/* track free pages over calls, shrink when necessary */
	/* truncate if necessary */

	heap_endscan(scan);
	heap_close(lovheap, AccessShareLock);
	
	_bitmap_relbuf(metabuf);
}

/*
 * Vacuum a single bitmap vector.
 *
 * We traverse the vector page by page, checking if any TIDs have been
 * reaped (via the callback). There are three cases:
 *
 * If a given word is literal and a TID is reaped, we flip the bit
 * from 1 to 0. If the whole word, when we finish, is 0, transform
 * it to a compressed word. If the previous word is compressed and is non-
 * match fill, we merge these two words.
 *
 * If the word is non-match fill, we first test if we can merge it with the
 * previous word. If not, we just copy it directly.
 *
 * If the word is match fill, we must iterate through the range and see if
 * any TIDs have been reaped. If we find a reaped TID, we have to break up
 * the fill word. This will result in 2 or 3 words replacing one word. That is,
 * If the first TID in the range is reaped, we'll create a new literal word and
 * have a fill word representing the rest of the range. If the reaped TID is
 * in the middle of the fill, we'll have an initial word representing the
 * initial matches, a literal word with the non-match and then a proceeding
 * word of matches again.
 *
 * It's reasonable that reaped TIDs might be clustered. So, instead of
 * breaking the fill word straight away, we construct a word for the initial
 * part of the range and then set a flag to indicate that we found a reaped 
 * TID. Once we find a non-reaped TID, we construct a word representing the 
 * non-match range and then continue processing the rest of the range.
 *
 * When we shrink or grow the index, we must physically shift data on the page.
 * Shrinking is not a problem, we just maintain it logically. If we need to
 * grow the storage (because we create a non-match in a match fill word) we 
 * either absorb the space between the logical write position and the read
 * position OR, if there is no such space, we must pull data off the end
 * of the page into 'overflow' storage and push the remaining data toward the
 * end of the page.
 */
static void
vacuum_vector(bmvacinfo vacinfo, IndexBulkDeleteCallback callback,
			  void *callback_state)
{
	/*
	 * Iterate over the bitmap vector. For each setbit, see if it's in the
	 * reaped tids (via the callback). Once we find a reaped tid, we continue 
	 * to iterate until we find a non-reaped tid. Then we patch things up.
	 *
	 * There are two ways we could do this: memmove() things around a lot
	 * on the live page or create a new page and overwrite the existing one.
	 * For now, we do the latter.
	 */
	bmvacstate state;

	state.cur_bitpos = 1;
	state.readwordno = 0;
	state.writewordno = 0;
	
	state.callback = callback;
	state.callback_state = callback_state;
	
	state.itr_blk = vacinfo.lovitem->bm_lov_head;
	state.curbuf = InvalidBuffer;

	state.ovrflwwordno = 0;

	state.curlov = vacinfo.lovitem;

	if (!BlockNumberIsValid(state.itr_blk))
	{
		elog(NOTICE, "invalid head, compword: %i, lastword: %i",
			 vacinfo.lovitem->bm_last_compword, vacinfo.lovitem->bm_last_word);
		return;
	}
		
	/* The outer loop iterates over each block in the vector */
	do
	{
		if (!BufferIsValid(state.curbuf))
		{
	   		state.curbuf = _bitmap_getbuf(vacinfo.info->index, state.itr_blk, 
										  BM_WRITE);
		}
		state.curbm = (BMBitmapVectorPage)PageGetContents(BufferGetPage(state.curbuf));
		state.curbmo = 
			(BMPageOpaque)PageGetSpecialPointer(BufferGetPage(state.curbuf));

#ifdef DEBUG_BMI
		elog(NOTICE, "words used: %i, comp %i, last %i", 
			 state.curbmo->bm_hrl_words_used,
			 vacinfo.lovitem->bm_last_compword, vacinfo.lovitem->bm_last_word);
#endif
		while (state.readwordno < state.curbmo->bm_hrl_words_used)
		{
			/* Fill word */
			if (IS_FILL_WORD(state.curbm->hwords, state.readwordno))
			{
				vacuum_fill_word(&state, BM_VAC_PAGE);
			}
			else
			{
				vacuum_literal_word(&state, BM_VAC_PAGE);
			}	
			state.readwordno++;
			state.writewordno++;

			/* 
			 * If we're reached the last word, see if there are any overflows
			 * and if so, merge them back into the page.
			 */
			vacuum_append_ovrflw_words(&state);
		}

		if (state.ovrflwwordno)
		{
			/* 
			 * We must merge the over flow into the next page. Write lock that
			 * page first so that no one can miss the data held privately
			 * by us.
			 */
			Buffer nbuf;
			elog(NOTICE, "---------");
			elog(NOTICE, "overflows!");
			elog(NOTICE, "---------");

			state.itr_blk = state.curbmo->bm_bitmap_next;
			_bitmap_wrtbuf(state.curbuf);
			state.curbuf = nbuf;

		}
		else
		{
			state.itr_blk = state.curbmo->bm_bitmap_next;
			_bitmap_wrtbuf(state.curbuf);
		}
	} while (BlockNumberIsValid(state.itr_blk));

	vacuum_last_words(&state);
}

static void
fill_matched(bmvacstate *state, uint64 start, uint64 end)
{
	if (start && start < end)
	{
		BM_WORD newword;
		uint64 len = end - start - 1;

		Assert(len > 0);
		
		if (len >= BM_WORD_SIZE)
		{
			/* set the new fill length */

			elog(NOTICE, "shrinking fill word. old len = "
				 "new len = %lli", len / BM_WORD_SIZE);
			
			newword = BM_MAKE_FILL_WORD(1, len / BM_WORD_SIZE);
			state->curbm->cwords[state->writewordno] = newword;
			HEADER_SET_FILL_BIT_ON(state->curbm->hwords,
								   state->writewordno);

			try_shrink_bitmap(state);
			progress_write_pos(state);

			len = len % BM_WORD_SIZE;
			start = end - len;
			newword = 0;
		}

		if (len)
		{
			uint64 i;
			
			/*
			 * We need to create a literal representation of the
			 * matches. If the current write word is fill, create
			 * a new word. If the existing word is literal, merge
			 * in our matches.
			 */
			if (IS_FILL_WORD(state->curbm->hwords, 
							 state->writewordno))
				progress_write_pos(state);
			
			newword = state->curbm->cwords[state->writewordno];

			for (i = start; i < state->cur_bitpos; i++)
			{
				if ((i % BM_WORD_SIZE) == 0)
				{
					progress_write_pos(state);
					newword = state->curbm->cwords[state->writewordno];
				}
				newword |= 1 << ((i % BM_WORD_SIZE) - 1);
			}
			try_shrink_bitmap(state);
		}
	}
}

static void
fill_reaped(bmvacstate *state, uint64 start, uint64 end)
{
	uint64 len = end - start;

	elog(NOTICE, "inserting fill worked for "
	 "reaped tids, from (%i, %i) to (%i, %i)",
			 BM_INT_GET_BLOCKNO(start),
			 BM_INT_GET_OFFSET(start),
			 BM_INT_GET_BLOCKNO(end),
			 BM_INT_GET_OFFSET(end));
	if (len < BM_WORD_SIZE)
	{
		if (IS_FILL_WORD(state->curbm->hwords, state->writewordno))
		{
			if (GET_FILL_BIT(state->curbm->cwords[state->writewordno]) == 0 ||
				state->curbm->cwords[state->writewordno])
			{
				/* 
				 * Consuming a word is enough to insert the fill, because the
				 * length is less than BM_WORD_SIZE.
				 */
				progress_write_pos(state);
			}
			else
			{
				/* match fill */
				progress_write_pos(state);
			}
		}
		else
		{
			/* 
			 * Literal word. Check if we can pull all the non-matches in this
			 * word.
			 */
			if (((start % BM_WORD_SIZE) - 1) + len > BM_WORD_SIZE)
			{
				progress_write_pos(state);
			}
		}
	}
	else
	{
		/* Fill and non-fill word */
		BM_WORD fillword = BM_MAKE_FILL_WORD(0, len / BM_WORD_SIZE);
		if (IS_FILL_WORD(state->curbm->hwords, state->writewordno))
		{
			if (GET_FILL_BIT(state->curbm->cwords[state->writewordno]) == 0 ||
				state->curbm->cwords[state->writewordno] == 0)
			{
				BM_WORD curword = state->curbm->cwords[state->writewordno];
				if (FILL_LENGTH(curword) + FILL_LENGTH(fillword) <
					MAX_FILL_LENGTH)
				{
					state->curbm->cwords[state->writewordno] += fillword;
				}
				else
				{
					fillword -= MAX_FILL_LENGTH -
						state->curbm->cwords[state->writewordno];
					progress_write_pos(state);
					state->curbm->cwords[state->writewordno] = fillword;
					HEADER_SET_FILL_BIT_ON(state->curbm->hwords,
										   state->writewordno);
				}
				len = len % BM_WORD_SIZE;
				if (len)
				{
					progress_write_pos(state);
				}
			}
		}
		else
		{
			progress_write_pos(state);
			state->curbm->cwords[state->writewordno] = fillword;
			HEADER_SET_FILL_BIT_ON(state->curbm->hwords,
								   state->writewordno);
		}
	}
}

static void
vacuum_fill_word(bmvacstate *state, bmVacType vactype)
{
	BM_WORD word = vactype_get_word(state, vactype);

	/*
	 * If the fill word is for non-matches, we do not have to
	 * check if there are any reaped TIDs. There wont be by
	 * definition.
	 */
	elog(NOTICE, "new word is FILL: %i", word);
	
	/* only vacuum non-match fill words if this is a physical page */
	if (GET_FILL_BIT(word) == 0 && vactype == BM_VAC_PAGE)
	{
		/* skip over */
		elog(NOTICE, "new word is non-match fill");

		/* if the current read pos is the same as the write pos, do nothing */
		if (state->readwordno != state->writewordno)
		{
			state->curbm->cwords[state->writewordno] = word;
			HEADER_SET_FILL_BIT_ON(state->curbm->hwords, state->writewordno);
			
		}
		progress_write_pos(state);
		try_shrink_bitmap(state);
	}
	else if (GET_FILL_BIT(word) == 1)
	{
		/*
		 * XXX: the call back does not take advantage of the
		 * fact that we know that this is a range of matches. In
		 * the future, we might have a different call back which
		 * can use a better search algorithm. For now, play
		 * dumb.
		 */
		bool found_reaped = false;
		uint64 start_setbit = state->cur_bitpos; /* start of match range */
		uint64 end = state->cur_bitpos + 
			(FILL_LENGTH(word) * BM_WORD_SIZE);

		state->start_reaped = 0;
		
		elog(NOTICE, "new word is match fill");

		elog(NOTICE, "testing match fill range. start = (%i, %i) "
			 "end = (%i, %i)",
			 BM_INT_GET_BLOCKNO(state->cur_bitpos),
			 BM_INT_GET_OFFSET(state->cur_bitpos),
			 BM_INT_GET_BLOCKNO(end),
			 BM_INT_GET_OFFSET(end));

		while (state->cur_bitpos < end)
		{
			ItemPointerData tid;

			ItemPointerSet(&tid, BM_INT_GET_BLOCKNO(state->cur_bitpos),
						  BM_INT_GET_OFFSET(state->cur_bitpos)); 
			
			elog(NOTICE, "testing fill tid (%i, %i)",
				 BM_INT_GET_BLOCKNO(state->cur_bitpos),
				 BM_INT_GET_OFFSET(state->cur_bitpos));

			if (state->callback(&tid, state->callback_state))
			{
				elog(NOTICE, "tid is reaped");
				/* 
				 * We found a match. We don't just break the fill
				 * word in to three. Instead, we shrink the
				 * original fill word and continue to loop
				 * until we find a set bit which isn't reaped,
				 * then we'll add a word reflecting the non-matches.
				 */
				
				found_reaped = true;
				
				fill_matched(state, start_setbit, state->cur_bitpos - 1);
				if (!state->start_reaped)
				{
					state->start_reaped = state->cur_bitpos;
					start_setbit = 0;
				}
			}
			else
			{
				/*
				 * If we're already seen a range of reaped TIDs, fill those in
				 * on the current word.
				 */
				if (state->start_reaped && 
					state->start_reaped < state->cur_bitpos - 1)
				{
					/* 
					 * insert fill word. remember, previous word
					 * might have been a fill word which we can
					 * extend.
					 */
					fill_reaped(state, state->start_reaped, 
								state->cur_bitpos - 1);
					
					state->start_reaped = 0;
					Assert(start_setbit == 0);
					start_setbit = state->cur_bitpos;
				}
				else
				{
					if (start_setbit == 0)
						start_setbit = state->cur_bitpos;
				}

				/* XXX: just do this logically!!! */
				word |= 1 << ((state->cur_bitpos % BM_WORD_SIZE) - 1);
				state->curbm->cwords[state->writewordno] = word;

				try_shrink_bitmap(state);

				/* roll over to a new word if need be */
				if (!IS_FILL_WORD(state->curbm->hwords, state->writewordno) &&
					(state->cur_bitpos % BM_WORD_SIZE) == 0)
				{
					progress_write_pos(state);
				}
				state->last_setbit = state->cur_bitpos;
			}
			state->cur_bitpos++;
		}
		if (!found_reaped)
		{
			elog(NOTICE, "didn't reap any, copy directly");
			/* only do this if we've got an on page word */
			if (vactype == BM_VAC_PAGE)
			{
				state->curbm->cwords[state->writewordno] = word;
				HEADER_SET_FILL_BIT_ON(state->curbm->hwords,
									   state->writewordno);
			}
			return;
		}
		else if(start_setbit)
		{
			fill_matched(state, start_setbit, state->cur_bitpos - 1);
		}
		else if(state->start_reaped)
		{
			fill_reaped(state, state->start_reaped,	state->cur_bitpos - 1);
		}

		/* 
		 * If this is last complete word or last word, we've just put the data
		 * for that word on the physical page so get it back.
		 */
		if (vactype == BM_VAC_LAST_COMPWORD || 
			vactype == BM_VAC_LAST_WORD)
		{
			BM_WORD newword = state->curbm->cwords[state->writewordno];

			switch(vactype)
			{
				case BM_VAC_LAST_COMPWORD:
					state->curlov->bm_last_compword = newword;
					state->curlov->lov_words_header &=
						BM_LAST_COMPWORD_BIT;
					break;
				case BM_VAC_LAST_WORD:
					state->curlov->bm_last_word = newword;
					state->curlov->lov_words_header &=
						BM_LAST_WORD_BIT;
					break;
				default:
					/* wont happen */
					break;
			}

			if (state->writewordno)
				state->writewordno--;
		}
	}
}

/*
 * Try to merge the current word with the previous word. This is only used
 * for vacuuming so we'll only shrink non-match words.
 */
static void
try_shrink_bitmap(bmvacstate *state)
{
	BM_WORD word = state->curbm->cwords[state->writewordno];

	/* we have no hope if there's no previous word */
	if (!(state->writewordno >= 1))
		return;
	
	if (word == LITERAL_ALL_ZERO)
	{
		BM_WORD prevword = state->curbm->cwords[state->writewordno - 1];
		
		/* check if earlier word was fill too */
		if (BM_WORD_IS_NON_MATCH_FILL(state->curbm, state->writewordno - 1) &&
			FILL_LENGTH(prevword) < MAX_FILL_LENGTH)
		{
			state->curbm->cwords[state->writewordno - 1]++;
			/* previous word absorbed current word, so step back a word */
			state->writewordno--;
		}
		else
		{
			state->curbm->cwords[state->writewordno] =
				BM_MAKE_FILL_WORD(0, 1);
			HEADER_SET_FILL_BIT_OFF(state->curbm->hwords,
									state->writewordno);
		}
	}
	else
	{
		BM_WORD prevword = state->curbm->cwords[state->writewordno - 1];

		if (!BM_WORD_IS_NON_MATCH_FILL(state->curbm, state->writewordno - 1))
		   return;
	
		if (FILL_LENGTH(word) + FILL_LENGTH(prevword) <= MAX_FILL_LENGTH)
		{
			state->curbm->cwords[state->writewordno - 1] +=
				FILL_LENGTH(word);
			
			/* previous word absorbed us, see above */
			state->writewordno--;
		}
		else
		{
			/* fill up previous word with non-matches and shrink current word */
			int16 diff = MAX_FILL_LENGTH - FILL_LENGTH(prevword);
			state->curbm->cwords[state->writewordno - 1] += MAX_FILL_LENGTH;
			state->curbm->cwords[state->writewordno] = word - diff;
		}
	}
}

static void
vacuum_literal_word(bmvacstate *state, bmVacType vactype)
{
	BM_WORD word;
	uint8 i;
	BM_WORD match = 1;

	word = vactype_get_word(state, vactype);

#ifdef DEBUG_BMI
	elog(NOTICE, "vacuuming literal word %i", word);
#endif
	for (i = 0; i < BM_WORD_SIZE; i++)
	{
		match <<= i;
		state->cur_bitpos++;
		if (word & match)
		{
			ItemPointerData tid;

			ItemPointerSet(&tid, BM_INT_GET_BLOCKNO(state->cur_bitpos),
						   BM_INT_GET_OFFSET(state->cur_bitpos));
#ifdef DEBUG_BMI
			elog(NOTICE, "found match for (%i, %i)",
				 BM_INT_GET_BLOCKNO(state->cur_bitpos),
				 BM_INT_GET_OFFSET(state->cur_bitpos));
#endif
			if (state->callback(&tid, state->callback_state))
			{
				/* turn the bit off, easy as that! */
				word |= ~match;
				elog(NOTICE, "inverted match for %i, word = %i",
					 i, word);
			}
			else
				state->last_setbit = state->cur_bitpos;
		}
	}
	put_vacuumed_literal_word(state, vactype, word);
}


/*
 * Check for a scenario where the next write would overwrite a block we
 * haven't read. Put words at the end of the storage into an overflow 
 * bitmap and shift everything to the right.
 */
static void
check_page_space(bmvacstate *state)
{
	elog(NOTICE, "checking page space: write pos: %i, read pos: %i",
		 state->writewordno, state->readwordno);

	if (state->writewordno > state->readwordno)
	{
		/* 
		 * We need to free up some space. There are two scenarios here:
		 * the page might not actually be full so we just shift things to
		 * the right and not worry about overflow; otherwise, the page is
		 * full so we just move the remaining words off the page into a new
		 * one and just tie things together. This is potentially inefficient
		 * but alternative methods require a lot of code. 
		 */
		uint16 from = 0;
		uint16 diff = 0;
		uint16 ovrflwwords = 0; /* number of words to put into overflow */

		/* first case */
		if (state->curbmo->bm_hrl_words_used < BM_NUM_OF_HRL_WORDS_PER_PAGE)
		{
			diff = BM_NUM_OF_HRL_WORDS_PER_PAGE - 
				state->curbmo->bm_hrl_words_used;
			from = state->readwordno;

			/* XXX: is there an off by one here? */
			memmove(&(state->curbm->cwords[from + diff]),
					&(state->curbm->cwords[state->readwordno]),
					state->curbmo->bm_hrl_words_used - from);
			memmove(&(state->curbm->hwords[(from + diff)/BM_WORD_SIZE]),
					&(state->curbm->hwords[from/BM_WORD_SIZE]),
				    (state->curbmo->bm_hrl_words_used - from)/BM_WORD_SIZE);
			/* 
			 * Now, we must change to read position to point to the new
			 * current word.
			 */
			state->readwordno += diff;
		}
		else
		{
			
	   		/*
		 	 * We can't do this the easy way,time to free some up. We take 
		 	 * BM_WORD_SIZE number of words at a time, because it's 
		 	 * convenient for managing the header: we just need to copy a 
		 	 * single word.
			 */

			diff = 
				BM_NUM_OF_HRL_WORDS_PER_PAGE - state->readwordno;
			if (diff > BM_WORD_SIZE)
				ovrflwwords = diff = BM_WORD_SIZE;
			else
				ovrflwwords = diff;
		}

		/* copy to overflow, if instructed */
		if (ovrflwwords)
		{
			uint16 oo = state->ovrflwwordno;
			state->ovrflw.hwords[oo/BM_WORD_SIZE] =	
				state->curbm->hwords[from/BM_WORD_SIZE];
			
			memcpy(&(state->ovrflw.cwords[oo]),
				   &(state->curbm->hwords[from]),
				   diff * sizeof(BM_WORD));
		}
		/* XXX: is there an off by one here? */
		memmove(&(state->curbm->cwords[from + diff]),
				&(state->curbm->cwords[from]),
				diff);

		state->curbm->hwords[(from + diff)] = state->curbm->hwords[from];

		state->readwordno += diff;
	}
}


/* 
 * Progress the write position pointer, filling the word with non-matches
 * and ensuring the write pointer doesn't overtake the read pointer.
 */

static void
progress_write_pos(bmvacstate *state)
{
	state->writewordno++;
	check_page_space(state);
	state->curbm->cwords[state->writewordno] = LITERAL_ALL_ZERO;
	HEADER_SET_FILL_BIT_OFF(state->curbm->hwords, state->writewordno);
}

/*
 * We must vacuum the last_word and last_compword in the LOV item.
 */
static void
vacuum_last_words(bmvacstate *state)
{
	/* 
	 * When initialised, the last complete word is set to LITERAL_ALL_ONE and
	 * it should never return to that again (because we compress it first).
	 * See _bitmap_formitem().
	 */
#ifdef DEBUG_BMI
	elog(NOTICE, "vacuuming last words");
	elog(NOTICE, "comp %i, last %i", state->curlov->bm_last_compword,
		 state->curlov->bm_last_word);
#endif
	if (state->curlov->bm_last_compword != LITERAL_ALL_ONE)
	{
		/* Is the word fill */
		if (BM_LAST_COMPWORD_IS_FILL(state->curlov))
		{
			if (GET_FILL_BIT(state->curlov->bm_last_compword) == 1)
			{
				elog(NOTICE, "match fill %i",
					 state->curlov->bm_last_compword);
			}
			/* If non-match fill, there's nothing to do */
		}
		else
		{
			vacuum_literal_word(state, BM_VAC_LAST_COMPWORD);
		}
	}

	/* 
	 * Now, we do the non-complete word. If it has no matches, don't 
	 * examine it.
	 */
	
	if (state->curlov->bm_last_word != 0)
	{
		if (BM_LASTWORD_IS_FILL(state->curlov))
			vacuum_fill_word(state, BM_VAC_LAST_WORD);
		else
			vacuum_literal_word(state, BM_VAC_LAST_WORD);
	}

	/* 
	 * If the last comp word and last word represent non-matches, we can
	 * truncate the bitmap.
	 */
	/* XXX: todo */
}

static BM_WORD
vactype_get_word(bmvacstate *state, bmVacType type)
{
	switch(type)
	{
		case BM_VAC_PAGE:
			return state->curbm->cwords[state->readwordno];
			break;
		case BM_VAC_LAST_COMPWORD:
			return state->curlov->bm_last_compword;
			break;
		case BM_VAC_LAST_WORD:
			return state->curlov->bm_last_word;
			break;
		default:
			elog(ERROR, "invalid bitmap vacuum state");
			return 0; /* not reached */
			break;
	}
	
}

static void
put_vacuumed_literal_word(bmvacstate *state, bmVacType type, BM_WORD word)
{
	switch(type)
	{
		case BM_VAC_PAGE:
			state->curbm->cwords[state->writewordno] = word;
			HEADER_SET_FILL_BIT_OFF(state->curbm->hwords, state->writewordno);
			try_shrink_bitmap(state);
			break;
		case BM_VAC_LAST_COMPWORD:
			state->curlov->bm_last_compword = word;
			state->curlov->lov_words_header &= ~BM_LAST_COMPWORD_BIT;
			break;
		case BM_VAC_LAST_WORD:
			state->curlov->bm_last_word = word;
			state->curlov->lov_words_header &= ~BM_LAST_WORD_BIT;
			break;
		default:
			elog(ERROR, "invalid bitmap vacuum state");
			break;
	}		
}

#if 0
/*
 * Either prepend or append overflow data to the current bitmap page.
 */
static void
merge_ovrflw(bmvacstate *state, bool append)
{
	uint16 start; /* start offset into the overflow */
	Buffer nbuf;

	/*
	 * If the current page hasn't used all of the available words, absorb those.
	 * Push any overflow into the overflow section.
	 */

	if (state->writewordno < (BM_NUM_OF_HRL_WORDS_PER_PAGE - 1))
	{



	}	

			if (BlockNumberIsValid(state->curbmo->bm_bitmap_next))
			{
				nbuf = _bitmap_getbuf(vacinfo.info->index,
									  state->curbmo->bm_bitmap_next,
									  BM_WRITE);
				elog(NOTICE, "adding overflow to %u",
					 state->curbmo->bm_bitmap_next);
			}
			else
			{
				/* Argh, we actually need a new page! */
				nbuf = _bitmap_getbuf(vacinfo.info->index, P_NEW, BM_WRITE);
		        _bitmap_init_bitmappage(nbuf);
				state->curlov->bm_lov_tail = state->curbmo->bm_bitmap_next = 
					BufferGetBlockNumber(nbuf);
				elog(NOTICE, "adding overflow to new block %u",
					 state->curbmo->bm_bitmap_next);
			}
}
#endif

static void
vacuum_append_ovrflw_words(bmvacstate *state)
{
	Assert(state->readwordno > 0);

	/*
	 * We want to copy BM_WORD_SIZE words at a time but we have to be careful
	 * of three things: a) we cannot go past BM_NUM_OF_HRL_WORDS_PER_PAGE,
	 * b) we cannot read past the end of the overflow words
	 */

}

