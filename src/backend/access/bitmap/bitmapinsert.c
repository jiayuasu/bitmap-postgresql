/*-------------------------------------------------------------------------
 *
 * bitmapinsert.c
 *	  Tuple insertion in the on-disk bitmap index.
 *
 * Copyright (c) 2007, PostgreSQL Global Development Group
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL$
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"
#include "miscadmin.h"

#include "access/genam.h"
#include "access/tupdesc.h"
#include "access/heapam.h"
#include "access/bitmap.h"
#include "parser/parse_oper.h"
#include "utils/builtins.h"
#include "utils/datum.h"
#include "storage/bufmgr.h" /* for buffer manager functions */
#include "utils/tqual.h" /* for SnapshotAny */
#include "utils/rel.h" /* for RelationGetDescr */
#include "utils/lsyscache.h" /* for get_opcode */

/*
 * The following structure along with BMTIDBuffer are used to buffer
 * words for tids * during index create -- bmbuild().
 */

/*
 * BMTIDLOVBuffer represents those bitmap vectors whose LOV item would be
 * stored on the specified lov_block. The array bufs stores the TIDs for
 * a distinct vector (see above). The index of the array we're upto tell
 * us the offset number of the LOV item on the lov_block.
 */

typedef struct BMTIDLOVBuffer
{
	BlockNumber lov_block;
	BMTIDBuffer *bufs[BM_MAX_LOVITEMS_PER_PAGE];
} BMTIDLOVBuffer;

static Buffer get_lastbitmappagebuf(Relation rel, BMLOVItem lovItem);
static void create_lovitem(Relation rel, Buffer metabuf, uint64 tidnum, 
						   TupleDesc tupDesc, 
						   Datum *attdata, bool *nulls,
						   Relation lovHeap, Relation lovIndex,
						   BlockNumber *lovBlockP, 
						   OffsetNumber *lovOffsetP, bool use_wal);
static void build_inserttuple(Relation index, uint64 tidnum,
    ItemPointerData ht_ctid,
    Datum *attdata, bool *nulls, BMBuildState *state);

static void inserttuple(Relation rel, Buffer metabuf, 
						uint64 tidnum, ItemPointerData ht_ctid, 
					    TupleDesc tupDesc, Datum* attdata,
					    bool *nulls, Relation lovHeap, 
						Relation lovIndex, ScanKey scanKey, 
						IndexScanDesc scanDesc, bool use_wal);
static void updatesetbit(Relation rel, 
						 Buffer lovBuffer, OffsetNumber lovOffset,
						 uint64 tidnum, bool use_wal);
static void updatesetbit_inword(BM_WORD word, uint64 updateBitLoc,
								uint64 firstTid, BMTIDBuffer *buf);
static void updatesetbit_inpage(Relation rel, uint64 tidnum,
								Buffer lovBuffer, OffsetNumber lovOffset,
								Buffer bitmapBuffer, uint64 firstTidNumber,
								bool use_wal);
static void insertsetbit(Relation rel, Buffer lovBuffer, OffsetNumber lovOffset,
			 			 uint64 tidnum, BMTIDBuffer *buf, bool use_wal);
static uint64 getnumbits(BM_WORD *contentWords, 
					     BM_WORD *headerWords, uint32 nwords);
static void findbitmappage(Relation rel, BMLOVItem lovitem,
					   uint64 tidnum,
					   Buffer *bitmapBufferP, uint64 *firstTidNumberP);
static void shift_header_bits(BM_WORD *words, uint32 numOfBits,
						  uint32 maxNumOfWords, uint32 startLoc,
						  uint32 numOfShiftingBits);
static void rshift_header_bits(BM_WORD *words, uint64 nwords,
							   uint32 bits);
static void lshift_header_bits(BM_WORD *words, uint64 nwords,
							   uint32 bits);
static void insert_newwords(BMTIDBuffer* words, uint32 insertPos,
							BMTIDBuffer* new_words, BMTIDBuffer* words_left);
static int16 mergewords(BMTIDBuffer* buf, bool lastWordFill);
static void buf_make_space(Relation rel,
					  BMTidBuildBuf *tidLocsBuffer, bool use_wal);
#ifdef DEBUG_BITMAP
static void verify_bitmappages(Relation rel, BMLOVItem lovitem);
#endif
static int16 buf_add_tid_with_fill(Relation rel, BMTIDBuffer *buf,
				   BlockNumber lov_block, OffsetNumber off,
				   uint64 tidnum, bool use_wal);
static uint16 buf_extend(BMTIDBuffer *buf);
static uint16 buf_ensure_head_space(Relation rel, BMTIDBuffer *buf,
								   BlockNumber lov_block, OffsetNumber off, 
								   bool use_wal);
static uint16 buf_free_mem(Relation rel, BMTIDBuffer *buf, 
			  			   BlockNumber lov_block, OffsetNumber off, 
			   bool use_wal, bool flush_hot_buffer);

#define BUF_INIT_WORDS 8 /* as good a point as any */

/* Debug helper functions */
void _debug_view_1(BMTidBuildBuf *x, const char *msg) ;
void _debug_view_2(BMTIDBuffer *x, const char *msg) ;


/*
 * get_lastbitmappagebuf() -- return the buffer for the last 
 *  bitmap page that is pointed by a given LOV item.
 *
 * The returned buffer will hold an exclusive lock.
 */
Buffer
get_lastbitmappagebuf(Relation rel, BMLOVItem lovitem)
{
	Buffer lastBuffer = InvalidBuffer;

	if (lovitem->bm_lov_head != InvalidBlockNumber)
		lastBuffer = _bitmap_getbuf(rel, lovitem->bm_lov_tail, BM_WRITE);

	return lastBuffer;
}

/*
 * getnumbits() -- return the number of bits included in the given
 * 	bitmap words.
 */
uint64
getnumbits(BM_WORD *contentWords, BM_WORD *headerWords, uint32 nwords)
{
	uint64	nbits = 0;
	uint32	i;

	for (i = 0; i < nwords; i++)
	{
		if (IS_FILL_WORD(headerWords, i))
			nbits += FILL_LENGTH(contentWords[i]) * BM_WORD_SIZE;
		else
			nbits += BM_WORD_SIZE;
	}

	return nbits;
}

/*
 * updatesetbit() -- update a set bit in a bitmap.
 *
 * This function finds the bit in a given bitmap vector whose bit location is
 * equal to tidnum, and changes this bit to 1.
 *
 * If this bit is already 1, then we are done. Otherwise, there are
 * two possibilities:
 * (1) This bit appears in a literal word. In this case, we simply change
 *     it to 1.
 * (2) This bit appears in a fill word with bit 0. In this case, this word
 *     may generate two or three words after changing the corresponding bit
 *     to 1, depending on the position of this bit.
 *
 * Case (2) will make the corresponding bitmap page to grow. The words after
 * this affected word in this bitmap page are shifted right to accommodate
 * the newly generated words. If this bitmap page does not have enough space
 * to hold all these words, the last few words will be shifted out of this
 * page. In this case, the next bitmap page is checked to see if there are
 * enough space for these extra words. If so, these extra words are inserted
 * into the next page. Otherwise, we create a new bitmap page to hold
 * these extra words.
 */
void
updatesetbit(Relation rel, Buffer lovBuffer, OffsetNumber lovOffset,
			 uint64 tidnum, bool use_wal)
{
	Page		lovPage;
	BMLOVItem	lovItem;
		
	uint64	tidLocation;
	uint16	insertingPos;

	uint64	firstTidNumber = 1;
	Buffer	bitmapBuffer = InvalidBuffer;

	lovPage = BufferGetPage(lovBuffer);
	lovItem = (BMLOVItem) PageGetItem(lovPage, 
		PageGetItemId(lovPage, lovOffset));

	/* Calculate the tid location in the last bitmap page. */
	tidLocation = lovItem->bm_last_tid_location;
	if (BM_LAST_COMPWORD_IS_FILL(lovItem))
		tidLocation -= (FILL_LENGTH(lovItem->bm_last_compword) *
					    BM_WORD_SIZE);
	else
		tidLocation -= BM_WORD_SIZE;

	/*
	 * If tidnum is in either bm_last_compword or bm_last_word,
	 * and this does not generate any new words, we simply
	 * need to update the lov item.
	 */
	if ((tidnum > lovItem->bm_last_tid_location) ||
		((tidnum > tidLocation) &&
		 ((lovItem->lov_words_header == BM_LOV_WORDS_NO_FILL) ||
		  (FILL_LENGTH(lovItem->bm_last_compword) == 1))))
	{
		START_CRIT_SECTION();

		MarkBufferDirty(lovBuffer);

		if (tidnum > lovItem->bm_last_tid_location)   /* bm_last_word */
		{
			insertingPos = (tidnum-1)%BM_WORD_SIZE;
			lovItem->bm_last_word |= (((BM_WORD)1)<<insertingPos);
		}
		else
		{
			if (FILL_LENGTH(lovItem->bm_last_compword) == 1)
				lovItem->bm_last_compword = 0;

			insertingPos = (tidnum - 1) % BM_WORD_SIZE;
			lovItem->bm_last_compword |= (((BM_WORD)1) << insertingPos);
			lovItem->lov_words_header = BM_LOV_WORDS_NO_FILL;
		}

		if (use_wal)
			_bitmap_log_bitmap_lastwords(rel, lovBuffer, lovOffset, lovItem);

		END_CRIT_SECTION();

		return;
	}

	/*
	 * Here, if tidnum is still in bm_last_compword, we know that
	 * bm_last_compword is a fill zero word with fill length greater
	 * than 1. This update will generate new words, we insert new words
	 * into the last bitmap page and update the lov item.
	 */
	if ((tidnum > tidLocation) && BM_LASTWORD_IS_FILL(lovItem))
	{
		/*
		 * We know that bm_last_compwords will be split into two
		 * or three words, depending on the splitting position.
		 */
		BMTIDBuffer buf;
		MemSet(&buf, 0, sizeof(buf));
		buf_extend(&buf);

		updatesetbit_inword(lovItem->bm_last_compword,
							tidnum - tidLocation - 1,
							tidLocation + 1, &buf);
		_bitmap_write_new_bitmapwords(rel, lovBuffer, lovOffset,
									  &buf, use_wal);

		_bitmap_free_tidbuf(&buf);

		return;
	}

	/*
	 * Now, tidnum is in the middle of the bitmap vector.
	 * We try to find the bitmap page that contains this bit,
	 * and update the bit.
	 */
	/* find the page that contains this bit. */
	findbitmappage(rel, lovItem, tidnum,
				   &bitmapBuffer, &firstTidNumber);

	/* trade in the read lock for a write lock */
	LockBuffer(bitmapBuffer, BUFFER_LOCK_UNLOCK);
	LockBuffer(bitmapBuffer, BM_WRITE);

	updatesetbit_inpage(rel, tidnum, lovBuffer, lovOffset,
						bitmapBuffer, firstTidNumber, use_wal);

	_bitmap_relbuf(bitmapBuffer);
}

/*
 * updatesetbit_inword() -- update the given bit to 1 in a given
 * 	word.
 *
 * The given word will generate at most three new words, depending on 
 * the position of the given bit to be updated. Make sure that the 
 * array 'words' has the size of 3 when you call this function. All new 
 * words will be put in this array, and the final number of new words is 
 * stored in '*numWordsP'. The bit location 'updateBitLoc' is relative to
 * the beginning of the given word, starting from 0.
 *
 * We assume that word is a fill zero word.
 */
void
updatesetbit_inword(BM_WORD word, uint64 updateBitLoc,
					uint64 firstTid, BMTIDBuffer *buf)
{
	uint64	numBits, usedNumBits;
	uint16	insertingPos;

	Assert(updateBitLoc < BM_WORD_SIZE*FILL_LENGTH(word));

	numBits = FILL_LENGTH(word) * BM_WORD_SIZE;
	usedNumBits = 0;
	if (updateBitLoc >= BM_WORD_SIZE)
	{
		firstTid += (updateBitLoc/BM_WORD_SIZE) * BM_WORD_SIZE;
		buf->cwords[buf->curword] =
			BM_MAKE_FILL_WORD(0, updateBitLoc/BM_WORD_SIZE);
		buf->last_tids[buf->curword] = firstTid - 1;
		buf->curword++;
		buf_extend(buf);
		buf->hwords[buf->curword/BM_WORD_SIZE] |=
			(((BM_WORD)1)<<(BM_WORD_SIZE - buf->curword));
		usedNumBits += (updateBitLoc/BM_WORD_SIZE) * BM_WORD_SIZE;
	}

	/* construct the literal word */
	insertingPos = updateBitLoc - usedNumBits;
	firstTid += BM_WORD_SIZE;
	buf->cwords[buf->curword] =
		((BM_WORD)0) | (((BM_WORD)1) << insertingPos);
	buf->last_tids[buf->curword] = firstTid - 1;
	buf->curword++;
	buf_extend(buf);
	usedNumBits += BM_WORD_SIZE;

	if (numBits > usedNumBits)
	{
		Assert((numBits - usedNumBits) % BM_WORD_SIZE == 0);

		firstTid += ((numBits - usedNumBits) / BM_WORD_SIZE) * BM_WORD_SIZE;
		buf->cwords[buf->curword] = BM_MAKE_FILL_WORD(0, 
									(numBits - usedNumBits) / BM_WORD_SIZE);
		buf->last_tids[buf->curword] = firstTid -1;
		buf->curword++;
		buf_extend(buf);
		buf->hwords[buf->curword/BM_WORD_SIZE] |=
			(1 << (BM_WORD_SIZE - buf->curword));
	}
}

/*
 * rshift_header_bits() -- 'in-place' right-shift bits in given words
 * 	'bits' bits.
 *
 * Assume that 'bits' is smaller than BM_WORD_SIZE. The right-most
 * 'bits' bits will be ignored.
 */
void
rshift_header_bits(BM_WORD* words, uint64 nwords,
				   uint32 bits)
{
	BM_WORD shifting_bits = 0;
	uint32 word_no;

	Assert(bits < BM_WORD_SIZE);

	for (word_no = 0; word_no < nwords; word_no++)
	{
		BM_WORD new_shifting_bits = 
			((BM_WORD)words[word_no]) << (BM_WORD_SIZE - bits);
		words[word_no] = (words[word_no] >> bits) | shifting_bits;

		shifting_bits = new_shifting_bits;
	}
}

/*
 * lshift_header_bits() -- 'in-place' left-shift bits in given words
 * 	'bits' bits.
 *
 * Assume that 'bits' is smaller than BM_WORD_SIZE. The left-most
 * 'bits' bits will be ignored.
 */
void
lshift_header_bits(BM_WORD* words, uint64 nwords,
				   uint32 bits)
{
	uint32 word_no;
	Assert(bits < BM_WORD_SIZE);

	for (word_no = 0; word_no < nwords; word_no++)
	{
		BM_WORD shifting_bits = 
			words[word_no] >> (BM_WORD_SIZE - bits);
		words[word_no] = ((BM_WORD)words[word_no]) << bits;

		if (word_no != 0)
			words[word_no - 1] |= shifting_bits;
	}
}



/*
 * shift_header_bits() -- right-shift bits after 'startLoc' for
 * 	'numofShiftingBits' bits.
 *
 * These bits are stored in an array of words with the word size of
 * BM_WORD_SIZE. This shift is done in-place. The maximum number of
 * words in this array is given. If the shifting causes the array not to
 * have enough space for all bits, the right-most overflow bits will be
 * discarded. The value 'startLoc' starts with 0.
 */
void
shift_header_bits(BM_WORD* words, uint32 numOfBits,
						  uint32 maxNumOfWords, uint32 startLoc,
						  uint32 numOfShiftingBits)
{
	uint32	startWordNo;
	uint32	endWordNo;
	uint32	wordNo;
	uint32	numOfFinalShiftingBits;
	BM_WORD tmpWord;

	Assert(startLoc <= numOfBits);
	Assert((numOfBits-1)/BM_WORD_SIZE < maxNumOfWords);

	startWordNo = startLoc/BM_WORD_SIZE;
	endWordNo = (numOfBits-1)/BM_WORD_SIZE;

	for (wordNo = endWordNo; wordNo > startWordNo; wordNo--)
	{
		/*
		 * obtain the last 'numOfShiftingBits' bits in the words[wordNo],
		 * and store them in the high-end of a word.
		 */
		tmpWord = (((BM_WORD)words[wordNo])<<
					(BM_WORD_SIZE-numOfShiftingBits));

		/* right-shift the original word 'numOfShiftingBits' bits. */
		words[wordNo] =	(((BM_WORD)words[wordNo])>>numOfShiftingBits);

		/* OR those shifted bits into the next word in the array. */
		if (wordNo < maxNumOfWords-1)
			words[wordNo + 1] |= tmpWord;
		
	}

	/* obtain bits after 'startLoc'.*/
	tmpWord = ((BM_WORD)(words[startWordNo]<<
				(startLoc%BM_WORD_SIZE)))>>(startLoc%BM_WORD_SIZE);

	words[startWordNo] = ((BM_WORD)(words[startWordNo]>>
			(BM_WORD_SIZE-startLoc%BM_WORD_SIZE)))<<
			(BM_WORD_SIZE-startLoc%BM_WORD_SIZE);

	numOfFinalShiftingBits = numOfShiftingBits;
	if (BM_WORD_SIZE - startLoc % BM_WORD_SIZE < numOfShiftingBits)
		numOfFinalShiftingBits = BM_WORD_SIZE - startLoc % BM_WORD_SIZE;

	words[startWordNo] |= (tmpWord>>numOfFinalShiftingBits);

	if (startWordNo < maxNumOfWords-1)
	{
		tmpWord = ((BM_WORD)(tmpWord << (BM_WORD_SIZE - numOfFinalShiftingBits)))>>
			(numOfShiftingBits - numOfFinalShiftingBits);
		words[startWordNo+1] |= tmpWord;
	}
}

/*
 * insert_newwords() -- insert a buffer of new words into a given buffer of
 *   words at a specified position.
 *
 * The new words will be inserted into the positions starting from
 * 'insertPos'(>=0). The original words from 'insertPos' will be shifted
 * to the right. If the given array does not have enough space to
 * hold all words, the last '(*numWordsP+numNewWords-maxNumWords)' words
 * will be stored in the buffer 'words_left', for which the caller should set
 * the enough space to hold these left words.
 *
 * All three buffers are specified as BMTIDBuffer objects, in which the following
 * fields are used:
 *   curword -- the number of content words in this buffer.
 *   num_cwords -- the maximum number of content words that are allowed.
 *   hwords -- the header words
 *   cwords -- the content words
 *
 * This function assumes that the number of new words is not greater than BM_WORD_SIZE.
 */
void
insert_newwords(BMTIDBuffer* words, uint32 insertPos,
				BMTIDBuffer* new_words, BMTIDBuffer* words_left)
{
	int32	wordNo;
	uint16  bitLoc;

	Assert(new_words->curword <= BM_WORD_SIZE);
	Assert(insertPos <= words->num_cwords);

	words_left->curword = 0;

	/* if there are no words in the original buffer, we simply copy the new words. */
	if (words->curword == 0)
	{
		memcpy(words->cwords, new_words->cwords, new_words->curword*sizeof(BM_WORD));
		memcpy(words->hwords, new_words->hwords,
			   BM_CALC_H_WORDS(new_words->curword) * sizeof(BM_WORD));
		words->curword = new_words->curword;

		return;
	}

	/*
	 * if insertPos is pointing to the position after the maximum position
	 * in this word, we simply copy the new words to leftContentWords.
	 */
	if (insertPos == words->num_cwords)
	{
		memcpy(words_left->cwords, new_words->cwords,
			   new_words->curword * sizeof(BM_WORD));
		memcpy(words_left->hwords, new_words->hwords,
			   BM_CALC_H_WORDS(new_words->curword) * sizeof(BM_WORD));
		words_left->curword = new_words->curword;

		return;
	}

	Assert(words->curword > 0);

	/* Calculate how many words left after this insert. */
	if (words->curword + new_words->curword > words->num_cwords)
		words_left->curword = words->curword + new_words->curword - words->num_cwords;
	MemSet(words_left->hwords, 0, BM_NUM_OF_HEADER_WORDS * sizeof(BM_WORD));

	/*
	 * Walk from the last word in the array back to 'insertPos'.
	 * If the word no + new_words->curword is greater than words->num_cwords,
	 * we store these words in words_left.
	 */
	for (wordNo=words->curword-1; wordNo>=0 && wordNo>=insertPos; wordNo--)
	{
		if (wordNo + new_words->curword >= words->num_cwords)
		{
			words_left->cwords[wordNo+new_words->curword-words->num_cwords] = 
				words->cwords[wordNo];
			if (IS_FILL_WORD(words->hwords, wordNo))
			{
				uint32		o = (int)wordNo/BM_WORD_SIZE;
				uint32		n = wordNo + new_words->curword - words->num_cwords;

				words_left->hwords[0] |= WORDNO_GET_HEADER_BIT(n);
				words->hwords[o] &= ~(WORDNO_GET_HEADER_BIT(wordNo));
			}
		}
		else
			words->cwords[wordNo + new_words->curword] = words->cwords[wordNo];
	}

	/* insert new words */
	for (wordNo=0; wordNo<new_words->curword; wordNo++)
	{
		if (insertPos+wordNo>= words->num_cwords)
		{
			uint32 	n = insertPos + wordNo - words->num_cwords;

			words_left->cwords[n] = new_words->cwords[wordNo];
			if (IS_FILL_WORD(new_words->hwords, wordNo))
				words_left->hwords[0] |= WORDNO_GET_HEADER_BIT(n);
		}
		else
			words->cwords[insertPos+wordNo] = new_words->cwords[wordNo];
	}

	/* right-shift the bits in the header words */
	shift_header_bits(words->hwords, words->curword, 
					  BM_NUM_OF_HEADER_WORDS, insertPos,
					  new_words->curword);

	/* set the newWords header bits */
	for (bitLoc = insertPos;
		 bitLoc < insertPos + new_words->curword && bitLoc < words->num_cwords;
		 bitLoc++)
	{
		if (IS_FILL_WORD(new_words->hwords, bitLoc-insertPos))
		{
			uint32		off = (uint32)bitLoc/BM_WORD_SIZE;

			words->hwords[off] |= WORDNO_GET_HEADER_BIT(bitLoc);
		}
	}

	words->curword += (new_words->curword - words_left->curword);	
}

/*
 * updatesetbit_inpage() -- update the given bit to 1 in a given
 *	bitmap page.
 *
 * The argument 'firstTidNumber' indicates the first tid location of
 * the bits stored in this page. This is necessary for locating the bit
 * of 'tidnum'.
 *
 * This update may generate new words that cause this page to overflow.
 * In this case, we will first check the next bitmap page have enough
 * space for these new words. If so, we update these two pages. Otherwise,
 * a new bitmap page is created.
 */
static void
updatesetbit_inpage(Relation rel, uint64 tidnum,
					Buffer lovBuffer, OffsetNumber lovOffset,
					Buffer bitmapBuffer, uint64 firstTidNumber,
					bool use_wal)
{
	Page 			bitmapPage;
	BMPageOpaque	bitmapOpaque;
	BMBitmapVectorPage		bitmap;
	Buffer			nextBuffer;
	Page			nextPage;
	BMPageOpaque	nextOpaque;
	BMBitmapVectorPage		nextBitmap;

	uint64			bitNo = 0;
	uint32			wordNo;
	uint32          free_words;
	BM_WORD		word = 0;
	bool			found = false;

	BMTIDBuffer     words;
	BMTIDBuffer     new_words;
	BMTIDBuffer     words_left;

	bool			new_page;
	bool			new_lastpage;
	int             word_no;

	bitmapPage = BufferGetPage(bitmapBuffer);
	bitmapOpaque = (BMPageOpaque)PageGetSpecialPointer(bitmapPage);

	bitmap = (BMBitmapVectorPage) PageGetContents(bitmapPage);
	bitNo = 0;

	/* Find the word that contains the bit of tidnum. */
	for (wordNo = 0; wordNo < bitmapOpaque->bm_hrl_words_used; wordNo++)
	{
		word = bitmap->cwords[wordNo];
		if (IS_FILL_WORD(bitmap->hwords, wordNo))
			bitNo += FILL_LENGTH(word) * BM_WORD_SIZE;
		else
			bitNo += BM_WORD_SIZE;

		if (firstTidNumber + bitNo - 1 >= tidnum)
		{
			found = true;
			break;		/* find the word */
		}
	}

	if(!found)
		elog(ERROR, "bitmap word uninitialized");

	Assert (wordNo <= bitmapOpaque->bm_hrl_words_used);

	/*
	 * If the word containing the updating bit is a literal word,
	 * we simply update the word, and return.
	 */
	if (!IS_FILL_WORD(bitmap->hwords, wordNo))
	{
		uint16 insertingPos = (tidnum - 1) % BM_WORD_SIZE;

		START_CRIT_SECTION();

		MarkBufferDirty(bitmapBuffer);

		bitmap->cwords[wordNo] |= (((BM_WORD)1)<<insertingPos);

		if (use_wal)
			_bitmap_log_updateword(rel, bitmapBuffer, wordNo);

		END_CRIT_SECTION();

		return;
	}

	/* If this bit is already 1, then simply return. */
	if (GET_FILL_BIT(word) == 1)
		return;

	firstTidNumber = firstTidNumber + bitNo -
					 FILL_LENGTH(word) * BM_WORD_SIZE;
		
	Assert(tidnum >= firstTidNumber);

	MemSet(&new_words, 0, sizeof(new_words));
	buf_extend(&new_words);
	updatesetbit_inword(word, tidnum - firstTidNumber, firstTidNumber,
						&new_words);

	/* Make sure that there are at most 3 new words. */
	Assert(new_words.curword <= 3);

	if (new_words.curword == 1)
	{
		uint32		off = wordNo/BM_WORD_SIZE;

		START_CRIT_SECTION();

		MarkBufferDirty(bitmapBuffer);

		bitmap->cwords[wordNo] = new_words.cwords[0];
		bitmap->hwords[off] &= ~WORDNO_GET_HEADER_BIT(wordNo);

		if (use_wal)
			_bitmap_log_updateword(rel, bitmapBuffer, wordNo);

		END_CRIT_SECTION();
		return;		
	}

	/*
	 * Check if this page has enough space for all new words. If so,
	 * replace this word with new words. Otherwise,
	 * we first check if the next page has enough space for all new words.
	 * If so, insert new words to the next page, otherwise,
	 * create a new page.
	 */
	free_words = BM_NUM_OF_HRL_WORDS_PER_PAGE -
			bitmapOpaque->bm_hrl_words_used;

	new_page = false;
	new_lastpage = false;
	nextBuffer = InvalidBuffer;

	if (free_words < new_words.curword - 1)
	{
		if (bitmapOpaque->bm_bitmap_next != InvalidBlockNumber)
		{
			nextBuffer = _bitmap_getbuf(rel, bitmapOpaque->bm_bitmap_next,
										BM_WRITE);
			nextPage = BufferGetPage(nextBuffer);
			nextOpaque = (BMPageOpaque)PageGetSpecialPointer(nextPage);
			free_words = BM_NUM_OF_HRL_WORDS_PER_PAGE -
				nextOpaque->bm_hrl_words_used;
		} else
		{
			new_lastpage = true;
		}
	}

	if (free_words < new_words.curword - 1)
	{
		if (BufferIsValid(nextBuffer))
			_bitmap_relbuf(nextBuffer);

		nextBuffer = _bitmap_getbuf(rel, P_NEW, BM_WRITE);
		_bitmap_init_bitmappage(nextBuffer);
		new_page = true;
		free_words = BM_NUM_OF_HRL_WORDS_PER_PAGE;
	}

	START_CRIT_SECTION();

	MarkBufferDirty(bitmapBuffer);
	if (BufferIsValid(nextBuffer))
		MarkBufferDirty(nextBuffer);

	if (new_lastpage)
	{
		Page 		lovPage;
		BMLOVItem	lovItem;
		MarkBufferDirty(lovBuffer);

		lovPage = BufferGetPage(lovBuffer);
		lovItem = (BMLOVItem) PageGetItem(lovPage, 
			PageGetItemId(lovPage, lovOffset));
		lovItem->bm_lov_tail = BufferGetBlockNumber(nextBuffer);
	}

	bitmap->cwords[wordNo] = new_words.cwords[0];
	if (tidnum - firstTidNumber + 1 <= BM_WORD_SIZE)
	{
		uint32		off = wordNo/BM_WORD_SIZE;

		bitmap->hwords[off] &= ~WORDNO_GET_HEADER_BIT(wordNo);
	}

	/* ignore the first word in new_words.cwords. */
	new_words.hwords[0] = ((BM_WORD)new_words.hwords[0]) << 1;
	for (word_no = 0; word_no < new_words.curword - 1; word_no++)
		new_words.cwords[word_no] = new_words.cwords[word_no+1];
	new_words.curword--;

	/* Create the buffer for the original words */
	MemSet(&words, 0, sizeof(words));
	words.cwords = bitmap->cwords;
	memcpy(words.hwords, bitmap->hwords,
		   BM_CALC_H_WORDS(bitmapOpaque->bm_hrl_words_used) * sizeof(BM_WORD));
	words.num_cwords = BM_NUM_OF_HRL_WORDS_PER_PAGE;
	words.curword = bitmapOpaque->bm_hrl_words_used;

	MemSet(&words_left, 0, sizeof(words_left));
	buf_extend(&words_left);

	insert_newwords(&words, wordNo + 1, &new_words, &words_left);

	/*
	 * We have to copy header words back to the page, and set the correct
	 * number of words in the page.
	 */
	bitmapOpaque->bm_hrl_words_used = words.curword;
	memcpy(bitmap->hwords, words.hwords,
		   BM_CALC_H_WORDS(bitmapOpaque->bm_hrl_words_used) * sizeof(BM_WORD));

	if (new_page)
	{
		nextPage = BufferGetPage(nextBuffer);
		nextOpaque = (BMPageOpaque)PageGetSpecialPointer(nextPage);
		nextBitmap = (BMBitmapVectorPage)PageGetContents(nextPage);

		nextOpaque->bm_last_tid_location = bitmapOpaque->bm_last_tid_location;
		nextOpaque->bm_bitmap_next = bitmapOpaque->bm_bitmap_next;
		bitmapOpaque->bm_bitmap_next = BufferGetBlockNumber(nextBuffer);
	}

	bitmapOpaque->bm_last_tid_location -=
		getnumbits(words_left.cwords, words_left.hwords, words_left.curword);
	
	if (words_left.curword > 0)
	{
		nextPage = BufferGetPage(nextBuffer);
		nextOpaque = (BMPageOpaque)PageGetSpecialPointer(nextPage);
		nextBitmap = (BMBitmapVectorPage)PageGetContents(nextPage);

		/* Create the buffer for the original words */
		MemSet(&words, 0, sizeof(words));
		words.cwords = nextBitmap->cwords;
		memcpy(words.hwords, nextBitmap->hwords,
			   BM_CALC_H_WORDS(nextOpaque->bm_hrl_words_used) * sizeof(BM_WORD));
		words.num_cwords = BM_NUM_OF_HRL_WORDS_PER_PAGE;
		words.curword = nextOpaque->bm_hrl_words_used;

		MemSet(&new_words, 0, sizeof(new_words));

		insert_newwords(&words, 0, &words_left, &new_words);

		/*
		 * We have to copy header words back to the page, and set the correct
		 * number of words in the page.
		 */
		nextOpaque->bm_hrl_words_used = words.curword;
		memcpy(nextBitmap->hwords, words.hwords,
			   BM_CALC_H_WORDS(nextOpaque->bm_hrl_words_used) * sizeof(BM_WORD));

		Assert(new_words.curword == 0);
	}

	if (use_wal)
		_bitmap_log_updatewords(rel, lovBuffer, lovOffset,
								bitmapBuffer, nextBuffer, new_lastpage);

	END_CRIT_SECTION();

	if (BufferIsValid(nextBuffer))
		_bitmap_relbuf(nextBuffer);

	_bitmap_free_tidbuf(&new_words);
	_bitmap_free_tidbuf(&words_left);
}

/*
 * findbitmappage() -- find the bitmap page that contains
 *	the given tid location, and obtain the first tid location
 * 	in this page.
 *
 * We assume that this tid location is not in bm_last_compword or
 * bm_last_word of its LOVItem.
 *
 * We will have read lock on the bitmap page we find.
 */
void
findbitmappage(Relation rel, BMLOVItem lovitem, uint64 tidnum,
			   Buffer *bitmapBufferP, uint64 *firstTidNumberP)
{
	BlockNumber nextBlockNo = lovitem->bm_lov_head;

	*firstTidNumberP = 1;

	while (BlockNumberIsValid(nextBlockNo))
	{
		Page bitmapPage;
		BMPageOpaque bitmapOpaque;

		*bitmapBufferP = _bitmap_getbuf(rel, nextBlockNo, BM_READ);
		bitmapPage = BufferGetPage(*bitmapBufferP);
		bitmapOpaque = (BMPageOpaque)
			PageGetSpecialPointer(bitmapPage);

		if (bitmapOpaque->bm_last_tid_location >= tidnum)
			return;   		/* find the page */

		(*firstTidNumberP) = bitmapOpaque->bm_last_tid_location + 1;
		nextBlockNo = bitmapOpaque->bm_bitmap_next;

		_bitmap_relbuf(*bitmapBufferP);
	}

	/*
	 * We can't find such a page. This should not happen.
	 * So we error out.
	 */
	elog(ERROR, "cannot find the bitmap page containing tid=%lld",
		 tidnum);
}

#ifdef DEBUG_BITMAP
/*
 * verify_bitmappages() -- verify if the bm_last_tid_location values
 * 	are valid in all bitmap pages. Only used during debugging.
 */
static void
verify_bitmappages(Relation rel, BMLOVItem lovitem)
{
	BlockNumber nextBlockNo = lovitem->bm_lov_head;
	uint64 tidnum = 0;

	while (BlockNumberIsValid(nextBlockNo))
	{
		Page bitmapPage;
		BMPageOpaque bitmapOpaque;
		Buffer bitmapBuffer;
		uint32 wordNo;
		BMBitmapVectorPage bitmap;

		bitmapBuffer = _bitmap_getbuf(rel, nextBlockNo, BM_READ);
		bitmapPage = BufferGetPage(bitmapBuffer);
		bitmapOpaque = (BMPageOpaque)
			PageGetSpecialPointer(bitmapPage);
		bitmap = (BMBitmapVectorPage) PageGetContents(bitmapPage);

		for (wordNo = 0; wordNo < bitmapOpaque->bm_hrl_words_used; wordNo++)
		{
			BM_WORD word = bitmap->cwords[wordNo];
			if (IS_FILL_WORD(bitmap->hwords, wordNo))
				tidnum += FILL_LENGTH(word) * BM_WORD_SIZE;
			else
				tidnum += BM_WORD_SIZE;

		}

		if (bitmapOpaque->bm_last_tid_location != tidnum)
			elog(ERROR, "bm_last_tid_location=%lld, tidnum=%lld",
                 bitmapOpaque->bm_last_tid_location, tidnum);

		nextBlockNo = bitmapOpaque->bm_bitmap_next;

		_bitmap_relbuf(bitmapBuffer);
	}
}

#endif /* DEBUG_BITMAP */

/*
 * mergewords() -- merge last two bitmap words based on the HRL compression
 * 	scheme. If these two words can not be merged, the last complete
 * 	word will be appended into the word array in the buffer.
 *
 * If the buffer is extended, this function returns the number
 * of bytes used.
 */
int16
mergewords(BMTIDBuffer *buf, bool lastWordFill)
{
	int16 bytes_used = 0;

	/* the last_tid in the complete word */
	uint64 last_tid = buf->last_tid - (buf->last_tid - 1) % BM_WORD_SIZE - 1;

#ifdef DEBUG_BMI
	_debug_view_2(buf,"[mergewords] BEGIN");
	elog(NOTICE,"lastWordFill = %d, last_tid = 0x%llx"
		 ,lastWordFill
		 ,last_tid);
#endif

	/* 
	 * If both words are LITERAL_ALL_ONE, then it is the very
	 * first invocation for this LOV item, so we skip mergewords.
	 */
	if (buf->last_compword == LITERAL_ALL_ONE
		&& buf->last_word == LITERAL_ALL_ONE) 
	  return bytes_used;

	/*
	 * If last_compword is LITERAL_ALL_ONE, it is not set yet.
	 * We move last_word to it.
	 */
	if (buf->last_compword == LITERAL_ALL_ONE)
	{
#ifdef DEBUG_BMI
	  elog(NOTICE,"[mergewords] CP1"
		   "\n\tbuf->last_compword == LITERAL_ALL_ONE");
#endif
		buf->last_compword = buf->last_word;
		buf->is_last_compword_fill = lastWordFill;
		if (lastWordFill)
			last_tid = FILL_LENGTH(buf->last_word) * BM_WORD_SIZE;
		else
			last_tid = BM_WORD_SIZE;

		buf->last_word = 0;
		buf->last_tid = last_tid;

#ifdef DEBUG_BMI
	_debug_view_2(buf,"[mergewords] END 1");
#endif
		return bytes_used;
	}
	/*
	 * If both words are fill words, and have the same fill bit,
	 * we increment the fill length of the last complete word by
	 * the fill length stored in the last word.
	 */
	if (buf->is_last_compword_fill && lastWordFill &&
		(GET_FILL_BIT(buf->last_compword) ==
		 GET_FILL_BIT(buf->last_word)))
	{
		BM_WORD lengthMerged;
			
		if (FILL_LENGTH(buf->last_compword) +
			FILL_LENGTH(buf->last_word) <
			MAX_FILL_LENGTH)
		{
			last_tid += FILL_LENGTH(buf->last_word)*BM_WORD_SIZE;
			buf->last_compword += FILL_LENGTH(buf->last_word);
			buf->last_word = LITERAL_ALL_ZERO;
			buf->last_tid = last_tid;

#ifdef DEBUG_BMI
			_debug_view_2(buf,"[mergewords] END 2");
#endif
			return bytes_used;
		}

		lengthMerged =
			MAX_FILL_LENGTH - FILL_LENGTH(buf->last_compword);
		buf->last_word -= lengthMerged;
		last_tid += lengthMerged * BM_WORD_SIZE;
		buf->last_compword += lengthMerged;
	}

	/*
	 * Here, these two words can not be merged together. We
	 * move the last complete word to the array, and set it to be the
	 * last word.
	 */

	/*
	 * When there are not enough space in the array of new words,
	 * we re-allocate a bigger space.
	 */
	bytes_used += buf_extend(buf);

	buf->cwords[buf->curword] = buf->last_compword;
	buf->last_tids[buf->curword] = last_tid;

	if (buf->is_last_compword_fill)
		buf->hwords[buf->curword/BM_WORD_SIZE] |=
			((BM_WORD)1) << (BM_WORD_SIZE - 
								 buf->curword % BM_WORD_SIZE - 1);

	buf->curword++;

	buf->last_compword = buf->last_word;
	buf->is_last_compword_fill = lastWordFill;
	if (buf->is_last_compword_fill)
		last_tid += FILL_LENGTH(buf->last_compword) * BM_WORD_SIZE;
	else
		last_tid += BM_WORD_SIZE;

	buf->last_word = 0;
	buf->last_tid = last_tid;

#ifdef DEBUG_BMI
	_debug_view_2(buf,"[mergewords] END 3");
#endif
	return bytes_used;
}

/*
 * _bitmap_write_new_bitmapwords() -- write a given buffer of new bitmap words
 *	into the end of bitmap page(s).
 *
 * If the last bitmap page does not have enough space for all these new
 * words, new pages will be allocated here.
 *
 * We consider a write to one bitmap page as one atomic-action WAL
 * record. The WAL record for the write to the last bitmap page also
 * includes updates on the lov item. Writes to the non-last
 * bitmap page are not self-consistent. We need to do some fix-up
 * during WAL logic replay.
 */
void
_bitmap_write_new_bitmapwords(Relation rel,
							  Buffer lovBuffer, OffsetNumber lovOffset,
							  BMTIDBuffer* buf, bool use_wal)
{
	Page		lovPage;
	BMLOVItem	lovItem;

	Buffer		bitmapBuffer;
	Page		bitmapPage;
	BMPageOpaque	bitmapPageOpaque;
		
	uint64		numFreeWords;
	uint64		words_written = 0;
	bool		isFirst = false;

	lovPage = BufferGetPage(lovBuffer);
	lovItem = (BMLOVItem) PageGetItem(lovPage, 
		PageGetItemId(lovPage, lovOffset));

	bitmapBuffer = get_lastbitmappagebuf(rel, lovItem);

	if (BufferIsValid(bitmapBuffer))
	{
		bitmapPage = BufferGetPage(bitmapBuffer);
		bitmapPageOpaque =
			(BMPageOpaque)PageGetSpecialPointer(bitmapPage);

		numFreeWords = BM_NUM_OF_HRL_WORDS_PER_PAGE -
					   bitmapPageOpaque->bm_hrl_words_used;
	}
	else
	{
		bitmapBuffer = _bitmap_getbuf(rel, P_NEW, BM_WRITE);
		_bitmap_init_bitmappage(bitmapBuffer);

		numFreeWords = BM_NUM_OF_HRL_WORDS_PER_PAGE;
	}

	while (numFreeWords < buf->curword - buf->start_wordno)
	{
		Buffer	newBuffer;

		bitmapPage = BufferGetPage(bitmapBuffer);
		bitmapPageOpaque =
			(BMPageOpaque)PageGetSpecialPointer(bitmapPage);

		newBuffer = _bitmap_getbuf(rel, P_NEW, BM_WRITE);
		_bitmap_init_bitmappage(newBuffer);

		START_CRIT_SECTION();

		MarkBufferDirty(bitmapBuffer);

		if (numFreeWords > 0)
		{
			words_written =
				_bitmap_write_bitmapwords(bitmapBuffer, buf);
		}

		bitmapPageOpaque->bm_bitmap_next = BufferGetBlockNumber(newBuffer);

		if (lovItem->bm_lov_head == InvalidBlockNumber)
		{
			isFirst = true;
			MarkBufferDirty(lovBuffer);
			lovItem->bm_lov_head = BufferGetBlockNumber(bitmapBuffer);
			lovItem->bm_lov_tail = lovItem->bm_lov_head;
		}

		if (use_wal)
			_bitmap_log_bitmapwords(rel, bitmapBuffer, lovBuffer, lovOffset,
									buf, words_written, buf->last_tid,
									BufferGetBlockNumber(newBuffer),
									false, isFirst);

#ifdef DEBUG_BMI
		elog(NOTICE,"[_bitmap_write_new_bitmapwords] CP1 (+=) : buf->start_wordno = %d , words_written = %llu"
			 ,buf->start_wordno,words_written
			 );
#endif		
		buf->start_wordno += words_written;

		END_CRIT_SECTION();

		_bitmap_relbuf(bitmapBuffer);

		bitmapBuffer = newBuffer;
		numFreeWords = BM_NUM_OF_HRL_WORDS_PER_PAGE;
	}

	/*
	 * Write remaining bitmap words to the last bitmap page and the
	 * lov page.
	 */
	START_CRIT_SECTION();

	MarkBufferDirty(lovBuffer);
	MarkBufferDirty(bitmapBuffer);

	if (buf->curword - buf->start_wordno > 0)
		words_written = _bitmap_write_bitmapwords(bitmapBuffer, buf);
	else
		words_written = 0;

	lovItem->bm_last_compword = buf->last_compword;
	lovItem->bm_last_word = buf->last_word;
	lovItem->lov_words_header = (buf->is_last_compword_fill) ? 
	   BM_LAST_COMPWORD_BIT	: BM_LOV_WORDS_NO_FILL;
	lovItem->bm_last_setbit = buf->last_tid;
	lovItem->bm_last_tid_location = buf->last_tid - buf->last_tid % BM_WORD_SIZE;
	lovItem->bm_lov_tail = BufferGetBlockNumber(bitmapBuffer);
	if (lovItem->bm_lov_head == InvalidBlockNumber)
	{
		isFirst = true;
		lovItem->bm_lov_head = lovItem->bm_lov_tail;
	}

	if (use_wal)
	{
		_bitmap_log_bitmapwords(rel, bitmapBuffer, lovBuffer,
								lovOffset, buf, words_written,
								buf->last_tid, InvalidBlockNumber, true,
								isFirst);
	}
#ifdef DEBUG_BMI
		elog(NOTICE,"[_bitmap_write_new_bitmapwords] CP2 (+=) : buf->start_wordno = %d, words_written = %llu"
			 "\n\tlovItem->bm_last_setbit = %llu"
			 "\n\tlovItem->bm_last_tid_location = %llu"
			 ,buf->start_wordno,words_written
			 ,lovItem->bm_last_setbit
			 ,lovItem->bm_last_tid_location
			 );
#endif		
	buf->start_wordno += words_written;

	Assert(buf->start_wordno == buf->curword);

	END_CRIT_SECTION();

	/* release bitmap buffer */
	_bitmap_relbuf(bitmapBuffer);	
}


/*
 * _bitmap_write_bitmapwords() -- Write an array of bitmap words into a given
 * bitmap page, and return how many words have been written in this call.
 *
 * The number of bitmap words writing to a given bitmap page is the maximum
 * number of words that can be appended into the page.
 *
 * We have the write lock on the given bitmap page.
 */
uint64
_bitmap_write_bitmapwords(Buffer bitmapBuffer, BMTIDBuffer *buf)
{
	uint64			startWordNo;
	Page			bitmapPage;
	BMPageOpaque	bitmapPageOpaque;
	BMBitmapVectorPage		bitmap;
	uint64			cwords;
	uint64			words_written;
	uint64			start_hword_no, end_hword_no;
	uint64			final_start_hword_no, final_end_hword_no;
	BM_WORD	   *hwords;
	uint64			num_hwords;
	uint32			start_hword_bit, end_hword_bit, final_start_hword_bit;

	startWordNo = buf->start_wordno;

	bitmapPage = BufferGetPage(bitmapBuffer);
	bitmapPageOpaque = (BMPageOpaque)PageGetSpecialPointer(bitmapPage);

	cwords = bitmapPageOpaque->bm_hrl_words_used;

	words_written = buf->curword - startWordNo;
	if (words_written > BM_NUM_OF_HRL_WORDS_PER_PAGE - cwords)
		words_written = BM_NUM_OF_HRL_WORDS_PER_PAGE - cwords;

	Assert (words_written > 0);

	/* Copy the content words */
	bitmap = (BMBitmapVectorPage) PageGetContents(bitmapPage);
	memcpy(bitmap->cwords + cwords,
		   buf->cwords + startWordNo,
		   words_written * sizeof(BM_WORD));

	/*
	 * Shift the header words in 'words' to match with the bit positions
	 * in the header words in this page, and then copy them.
	 */
	start_hword_no = startWordNo/BM_WORD_SIZE;
	end_hword_no = (startWordNo + words_written - 1) / BM_WORD_SIZE;
	num_hwords = end_hword_no - start_hword_no + 1;

	hwords = (BM_WORD*)
		palloc0((num_hwords + 1) * sizeof(BM_WORD));

	memcpy(hwords, buf->hwords + start_hword_no,
			num_hwords * sizeof(BM_WORD));

	/* clean up the first and last header words */
	start_hword_bit = startWordNo % BM_WORD_SIZE;
	end_hword_bit = (startWordNo + words_written - 1) % BM_WORD_SIZE;

	hwords[0] = ((BM_WORD)(hwords[0] << start_hword_bit)) >>
				start_hword_bit;
	hwords[num_hwords - 1] = (hwords[num_hwords - 1] >>
			(BM_WORD_SIZE - end_hword_bit - 1)) <<
			(BM_WORD_SIZE - end_hword_bit - 1);

	final_start_hword_bit = cwords % BM_WORD_SIZE;

	if (final_start_hword_bit > start_hword_bit)
	{
		/* right-shift 'final-start_hword_bit - start_hword_bit' */
		rshift_header_bits(hwords, num_hwords + 1,
						   final_start_hword_bit - start_hword_bit);
	}
	else if (final_start_hword_bit < start_hword_bit)
	{
		/* left-shift 'start_hword_bit - final_start_hword_bit' */
		lshift_header_bits(hwords, num_hwords,
						   start_hword_bit - final_start_hword_bit);
	}

	/* copy the header bits */
	final_start_hword_no = cwords / BM_WORD_SIZE;
	final_end_hword_no = (cwords + words_written - 1) / BM_WORD_SIZE;

	bitmap->hwords[final_start_hword_no] |= hwords[0];
	memcpy(bitmap->hwords+(final_start_hword_no + 1),
		   hwords + 1,
		   (final_end_hword_no - final_start_hword_no) *
			sizeof(BM_WORD));

	bitmapPageOpaque->bm_hrl_words_used += words_written;
	bitmapPageOpaque->bm_last_tid_location =
		buf->last_tids[startWordNo + words_written-1];

	pfree(hwords);

	return words_written;
}

/*
 * create_lovitem() -- create a new LOV item.
 *
 * Create a new LOV item and append this item into the last LOV page.
 * Each LOV item is associated with one distinct value for attributes
 * to be indexed. This function also inserts this distinct value along
 * with this new LOV item's block number and offsetnumber into the
 * auxiliary heap and its b-tree of this bitmap index.
 *
 * This function returns the block number and offset number of this
 * new LOV item.
 *
 * The caller should have an exclusive lock on metabuf.
 */
static void
create_lovitem(Relation rel, Buffer metabuf, uint64 tidnum,
			   TupleDesc tupDesc, Datum *attdata, bool *nulls,
			   Relation lovHeap, Relation lovIndex, BlockNumber *lovBlockP, 
			   OffsetNumber *lovOffsetP, bool use_wal)
{

	const int numOfAttrs = tupDesc->natts; /* number of attributes */
	Page page = BufferGetPage(metabuf); /* temporary page variable */
	BMMetaPage metapage; /* Meta page */

	/* Current LOV buffer and page */
	Buffer currLovBuffer;
	Page currLovPage;

	BMLOVItem lovitem; /* new LOV item */
	OffsetNumber itemSize; /* LOV item size */
	bool is_new_lov_blkno = false; /* do we have a new page for this item */

	Datum* lovDatum; /* array of values (per each attribute) */
	bool* lovNulls; /* is NULL flag for each attribute */

	/* Get the last LOV page. Meta page should be locked. */
	metapage = (BMMetaPage) PageGetContents(page);
	*lovBlockP = metapage->bm_lov_lastpage;

	/* Get the current LOV buffer and page */
	currLovBuffer = _bitmap_getbuf(rel, *lovBlockP, BM_WRITE);
	currLovPage = BufferGetPage(currLovBuffer);

	lovitem = _bitmap_formitem(tidnum);
	*lovOffsetP = OffsetNumberNext(PageGetMaxOffsetNumber(currLovPage));
	itemSize = sizeof(BMLOVItemData);

	/*
	 * If there is not enough space in the last LOV page for
	 * a new item, create a new LOV page, and update the metapage.
	 */
	if (itemSize > PageGetFreeSpace(currLovPage))
	{
	Buffer newLovBuffer;

	/* create a new LOV page */
	newLovBuffer = _bitmap_getbuf(rel, P_NEW, BM_WRITE);
	_bitmap_init_lovpage(newLovBuffer);

#if 0
		START_CRIT_SECTION();

		if(use_wal)
			_bitmap_log_newpage(rel, XLOG_BITMAP_INSERT_NEWLOV, 
								newLovBuffer);
		END_CRIT_SECTION();
#endif

	_bitmap_relbuf(currLovBuffer);

	currLovBuffer = newLovBuffer;
	currLovPage = BufferGetPage(currLovBuffer);

	is_new_lov_blkno = true;
	}

	START_CRIT_SECTION();

	if (is_new_lov_blkno)
	{
	MarkBufferDirty(metabuf);
	metapage->bm_lov_lastpage = BufferGetBlockNumber(currLovBuffer);
	}

	MarkBufferDirty(currLovBuffer);

	*lovOffsetP = OffsetNumberNext(PageGetMaxOffsetNumber(currLovPage));
	*lovBlockP = BufferGetBlockNumber(currLovBuffer);

	/* Allocate a new Item */
	lovDatum = palloc0((numOfAttrs + 2) * sizeof(Datum));
	lovNulls = palloc0((numOfAttrs + 2) * sizeof(bool));
	memcpy(lovDatum, attdata, numOfAttrs * sizeof(Datum));
	memcpy(lovNulls, nulls, numOfAttrs * sizeof(bool));
	lovDatum[numOfAttrs] = Int32GetDatum(*lovBlockP); /* Block number */
	lovDatum[numOfAttrs + 1] = Int16GetDatum(*lovOffsetP); /* Offset */
	lovNulls[numOfAttrs] = false;
	lovNulls[numOfAttrs + 1] = false;

	/* Insert the LOV in the HEAP and the LOV btree index */
	_bitmap_insert_lov(lovHeap, lovIndex, lovDatum, lovNulls, use_wal);

	if (PageAddItem(currLovPage, (Item)lovitem, itemSize, *lovOffsetP,
	false, false) == InvalidOffsetNumber)

/*
	if (PageAddItem(currLovPage, (Item)lovitem, itemSize, *lovOffsetP,
	false) == InvalidOffsetNumber)
		ereport(ERROR,
		(errcode(ERRCODE_INTERNAL_ERROR),
		errmsg("failed to add LOV item to \"%s\"",
		RelationGetRelationName(rel))));
*/
	/* Log the insertion */
	if(use_wal)
	_bitmap_log_lovitem(rel, currLovBuffer, *lovOffsetP, lovitem,
		metabuf, is_new_lov_blkno);

	END_CRIT_SECTION();

	_bitmap_relbuf(currLovBuffer);

	pfree(lovitem);
	pfree(lovDatum);
	pfree(lovNulls);
}

/*
 * When building an index we try and buffer calls to write tids to disk
 * as it will result in lots of I/Os.
 */

static void
buf_add_tid(Relation rel, BMTidBuildBuf *tids, uint64 tidnum, 
			BMBuildState *state, BlockNumber lov_block, OffsetNumber off)
{
	BMTIDBuffer *buf;
	BMTIDLOVBuffer *lov_buf = NULL;

#ifdef DEBUG_BMI
	_debug_view_1(tids,"CP1");
#endif
	/* If we surpass maintenance_work_mem, free some space from the buffer */
	if (tids->byte_size >= maintenance_work_mem * 1024L)
		buf_make_space(rel, tids, state->use_wal);

	/*
	 * tids is lazily initialized. If we do not have a current LOV block 
	 * buffer, initialize one.
	 */
	if(!BlockNumberIsValid(tids->max_lov_block) || 
	   tids->max_lov_block < lov_block)
	{
		/*
		 * XXX: We're currently not including the size of this data structure
		 * in out byte_size count... should we?
		 */
		lov_buf = palloc(sizeof(BMTIDLOVBuffer));
		lov_buf->lov_block = lov_block;
		MemSet(lov_buf->bufs, 0, BM_MAX_LOVITEMS_PER_PAGE * sizeof(BMTIDBuffer *));
		tids->max_lov_block = lov_block;
		
		/*
		 * Add the new LOV buffer to the list head. It seems reasonable that
		 * future calls to this function will want this lov_block rather than
		 * older lov_blocks.
		 */
		tids->lov_blocks = lcons(lov_buf, tids->lov_blocks);
	}
	else
	{
		ListCell *cell;
		
		foreach(cell, tids->lov_blocks)
		{
			BMTIDLOVBuffer *tmp = lfirst(cell);
			if(tmp->lov_block == lov_block)
			{
				lov_buf = tmp;
				break;
			}
		}
	}
	
	Assert(lov_buf);
	Assert(off - 1 < BM_MAX_LOVITEMS_PER_PAGE);

	if (lov_buf->bufs[off - 1])
	{

		buf = lov_buf->bufs[off - 1];

		buf_add_tid_with_fill
		  (rel, buf, lov_block, off, 
							  tidnum, state->use_wal);
	}
	else
	{
		/* no pre-existing buffer found, create a new one */
		Buffer lovbuf;
		Page page;
		BMLOVItem lovitem;
		uint16 bytes_added;
		
		buf = (BMTIDBuffer *)palloc0(sizeof(BMTIDBuffer));

#ifdef DEBUG_BMI
		elog(NOTICE,"[buf_add_tid] create new buf - CP1"
			 "\n\tlast_tid = 0x%llx"
			 "\n\tlast_compword = %u"
			 "\n\tlast_word = %d"
			 ,buf->last_tid
			 ,buf->last_compword
			 ,buf->last_word
			 );
#endif
		
		lovbuf = _bitmap_getbuf(rel, lov_block, BM_READ);
		page = BufferGetPage(lovbuf);
		lovitem = (BMLOVItem)PageGetItem(page, PageGetItemId(page, off));

		buf->last_tid = lovitem->bm_last_setbit;
#ifdef DEBUG_BMI
		elog(NOTICE,"[buf_add_tid] create new buf - CP1.1"
			 "\n\tlast_tid = 0x%llx"
			 "\n\tlast_compword = %u"
			 "\n\tlast_word = %d"
			 ,buf->last_tid
			 ,buf->last_compword
			 ,buf->last_word
			 );
#endif
		buf->last_compword = lovitem->bm_last_compword;
#ifdef DEBUG_BMI
		elog(NOTICE,"[buf_add_tid] create new buf - CP1.2"
			 "\n\tlast_tid = 0x%llx"
			 "\n\tlast_compword = %u"
			 "\n\tlast_word = %d"
			 ,buf->last_tid
			 ,buf->last_compword
			 ,buf->last_word
			 );
#endif
		buf->last_word = lovitem->bm_last_word;
		buf->is_last_compword_fill = BM_LAST_COMPWORD_IS_FILL(lovitem);

#ifdef DEBUG_BMI
		elog(NOTICE,"[buf_add_tid] create new buf - CP2"
			 "\n\tlast_tid = 0x%llx"
			 "\n\tlast_compword = %u"
			 "\n\tlast_word = %d"
			 ,buf->last_tid
			 ,buf->last_compword
			 ,buf->last_word
			 );
#endif

		_bitmap_relbuf(lovbuf); /* we don't care about locking */

		MemSet(buf->hwords, 0, BM_NUM_OF_HEADER_WORDS * sizeof(BM_WORD));

		/* initialisation of HOT buffer data */
		buf->hot_buffer_count=0;
		buf->hot_buffer_last_offset=0;
		buf->hot_buffer_block=InvalidBlockNumber;
		MemSet(buf->hot_buffer, 0, BM_SIZEOF_HOT_BUFFER * sizeof(BM_WORD));

		bytes_added = buf_extend(buf);

		buf->curword = 0;
		buf->start_wordno = 0;

		buf_add_tid_with_fill
		  (rel, buf, lov_block, off, tidnum, 
							  state->use_wal);

		lov_buf->bufs[off - 1] = buf;
		tids->byte_size += bytes_added;
	}
}

/*
 * hot_buffer_flush()
 */
static int16
hot_buffer_flush(Relation rel, BMTIDBuffer *buf,
		 BlockNumber lov_block, OffsetNumber off,
		 bool use_wal, bool merge_words)
{
  int i;
  int16 bytes_used = 0;

#ifdef DEBUG_BMI
  elog(NOTICE,"[hot_buffer_flush] BEGIN"
	   "\n\tBM_SIZEOF_HOT_BUFFER = %d"
	   "\n\thot_buffer_block = %04x"
	   "\n\thot_buffer_count = %d"
	   ,BM_SIZEOF_HOT_BUFFER
	   ,buf->hot_buffer_block
	   ,buf->hot_buffer_count);
#endif

#ifdef DEBUG_BMI
  /* display buffer contents */

  Assert(BM_WORD_SIZE==16);
  /* currently there's no need to be more general, and this is only
	 for debug purposes */

  for (i = 0 ; i < BM_SIZEOF_HOT_BUFFER ; i += 4) {
	if (BM_SIZEOF_HOT_BUFFER - i >= 4) {
	  elog(NOTICE,"[hot_buffer_flush] %02d-%02d : %04x %04x %04x %04x"
	   ,i,i+3
	   ,buf->hot_buffer[i]
	   ,buf->hot_buffer[i+1]
	   ,buf->hot_buffer[i+2]
	   ,buf->hot_buffer[i+3]
	   );	 
	  ;
	} else {
	  if (BM_SIZEOF_HOT_BUFFER - i == 3) {
	elog(NOTICE,"[hot_buffer_flush] %02d-%02d : %04x %04x %04x"
		 ,i,i+2
		 ,buf->hot_buffer[i]
		 ,buf->hot_buffer[i+1]
		 ,buf->hot_buffer[i+2]
		 );	   
	;
	  } else {
	elog(ERROR,"[hot_buffer_flush] INTERNAL ERROR: check out BM_SIZEOF_HOT_BUFFER");
	  }}}
#endif

  /* write the buffer to disk */
  if (1) { /* only to declare variables here */
	ItemPointerData _ctid ;
	int max_offset;
	bool merge_words = true;
	ItemPointerSetBlockNumber(&_ctid, buf->hot_buffer_block);
	for(i=0; i<BM_SIZEOF_HOT_BUFFER; i++) {
	  max_offset = Min(buf->hot_buffer_last_offset, (i+1)*BM_WORD_SIZE);
	  ItemPointerSetOffsetNumber(&_ctid, max_offset);
	  buf->last_tid = BM_IPTR_TO_INT(&_ctid);

	  /*
	   * don't merge the very last word, and also don't loop any more
	   */
	  if (buf->hot_buffer_last_offset <= (i+1) * BM_WORD_SIZE)
	merge_words=false;

#ifdef DEBUG_BMI
	  elog(NOTICE,"[hot_buffer_flush] CP0"
	   "\n\tbuf->hot_buffer_last_offset = %d"
	   "\n\ti = %d"
	   ,buf->hot_buffer_last_offset
	   ,i
	   );
#endif	  
	  bytes_used -= buf_ensure_head_space(rel, buf, lov_block, off, use_wal);
	  switch(buf->hot_buffer[i]) {
	  case LITERAL_ALL_ONE:
	buf->last_word = BM_MAKE_FILL_WORD(1,1);
	if(merge_words) {
#ifdef DEBUG_BMI
	  elog(NOTICE,"[hot_buffer_flush] CP1 merge_words");
#endif	  
	  if (merge_words) 
		bytes_used += mergewords(buf, true);	
	}
	break;
	  case LITERAL_ALL_ZERO:
	buf->last_word = BM_MAKE_FILL_WORD(0,1);
	if(merge_words) {
#ifdef DEBUG_BMI
	  elog(NOTICE,"[hot_buffer_flush] CP2 merge_words");
#endif	  
	  if (merge_words) 
		bytes_used += mergewords(buf, true);	
	}
	break;		
	  default:
	buf->last_word = buf->hot_buffer[i];
	if(merge_words) {
#ifdef DEBUG_BMI
	  elog(NOTICE,"[hot_buffer_flush] CP3 merge_words");
#endif	  
	  if (merge_words) 
		bytes_used += mergewords(buf, false);			 
	}
	  }
	  if (merge_words == false) 
	break;
	}
  }

  /* reset the buffer */
  for(i=0; i < BM_SIZEOF_HOT_BUFFER; i++) {
	buf->hot_buffer[i]=(BM_WORD)0;
  }
  buf->hot_buffer_count=0;

  return bytes_used;
}

/*
 * buf_add_tid_with_fill() -- Worker for buf_add_tid().
 *
 * Return how many bytes are used. Since we move words to disk when
 * there is no space left for new header words, this returning number
 * can be negative.
 */
static int16
buf_add_tid_with_fill(Relation rel, BMTIDBuffer *buf,
			  BlockNumber lov_block, OffsetNumber off,
			  uint64 tidnum, bool use_wal)
{
	int16 bytes_used = 0;
	BlockNumber _blockno = BM_INT_GET_BLOCKNO(tidnum);
	OffsetNumber _offset = BM_INT_GET_OFFSET(tidnum);
#ifdef DEBUG_BMI
	static int j=0;
#endif

#ifdef DEBUG_BMI
	if (j==1000) {
	  j=0;
	  _debug_view_2(buf,"[buf_add_tid_with_fill] BEGIN");
	  elog(NOTICE,"[buf_add_tid_with_fill] BEGIN"
		   "\n\ttidnum == 0x%08llx"
		   "\n\t_blockno == %08x"
		   "\n\t_offset	 == %04x"
		   ,tidnum
		   ,_blockno
		   ,_offset
		   );
	} else
	  j++;
#endif

  /* Checking if block number has changed */
  if (_blockno != buf->hot_buffer_block) {
	if (buf->hot_buffer_block != InvalidBlockNumber) {
	  buf->hot_buffer_last_offset = BM_MAX_HTUP_PER_PAGE;
	  hot_buffer_flush(rel,buf,lov_block,off,use_wal,true);
	}
#ifdef DEBUG_BMI
	elog(NOTICE,"[buf_add_tid_with_fill] updating hot_buffer_block"
	 "\n\thot_buffer_block == %08x"
	 "\n\t_blockno == %08x"
	 ,buf->hot_buffer_block
	 ,_blockno
	 );
#endif
	buf->hot_buffer_block = _blockno;
  }

  /* setting the bit */
  buf->hot_buffer[(_offset-1) / BM_WORD_SIZE] |= (((unsigned char)1) << ((_offset-1) % BM_WORD_SIZE));
  buf->hot_buffer_count ++;
  if (buf->hot_buffer_last_offset < _offset) 
	buf->hot_buffer_last_offset = _offset;
#ifdef DEBUG_BMI
  elog(NOTICE,"[buf_add_tid_with_fill] setting bit in hot_buffer"
	   "\n\t(_offset-1) / BM_WORD_SIZE == %d"
	   "\n\t(_offset-1) %% BM_WORD_SIZE == %d"
	   ,(_offset-1) / BM_WORD_SIZE
	   ,(_offset-1) % BM_WORD_SIZE
	   );
#endif

	return bytes_used;
}

/*
 * buf_ensure_head_space() -- If there is no space in the header words,
 * move words in the given buffer to disk and free the existing space,
 * and then allocate new space for future new words.
 *
 * The number of bytes freed are returned.
 */
static uint16
buf_ensure_head_space(Relation rel, BMTIDBuffer *buf, 
					  BlockNumber lov_block, OffsetNumber off, bool use_wal)
{
	uint16 bytes_freed = 0;

	if (buf->curword >= (BM_NUM_OF_HEADER_WORDS * BM_WORD_SIZE))
	{
#ifdef DEBUG_BMI
	  _debug_view_2(buf,"[buf_ensure_head_space] freeing bytes");
#endif
	  bytes_freed = buf_free_mem(rel, buf, lov_block, off, use_wal, false);
		bytes_freed -= buf_extend(buf);
	}

	return bytes_freed;
}

/*
 * buf_extend() -- Enlarge the memory allocated to a buffer.
 * Return how many bytes are added to the buffer.
 */
static uint16
buf_extend(BMTIDBuffer *buf)
{
	uint16 bytes;
	uint16 size;
	
#ifdef DEBUG_BMI
	elog(NOTICE,"[buf_extend] BEGIN");
#endif
	if (buf->num_cwords > 0 && buf->curword < buf->num_cwords - 1)
		return 0; /* already large enough */

#ifdef DEBUG_BMI
	elog(NOTICE,"[buf_extend] not large enough");
#endif

	if(buf->num_cwords == 0)
	{
		size = BUF_INIT_WORDS;
		buf->cwords = (BM_WORD *)
			palloc0(BUF_INIT_WORDS * sizeof(BM_WORD));
		buf->last_tids = (uint64 *)palloc0(BUF_INIT_WORDS * sizeof(uint64));
		bytes = BUF_INIT_WORDS * sizeof(BM_WORD) +
			BUF_INIT_WORDS * sizeof(uint64);
	}
	else
	{
		size = buf->num_cwords;
		buf->cwords = repalloc(buf->cwords, 2 * size * sizeof(BM_WORD));
		MemSet(buf->cwords + size, 0, size * sizeof(BM_WORD));
		buf->last_tids = repalloc(buf->last_tids, 2 * size * sizeof(uint64));
		MemSet(buf->last_tids + size, 0, size * sizeof(uint64));
		bytes = 2 * size * sizeof(BM_WORD) +
			2 * size * sizeof(uint64);
	}
	buf->num_cwords += size;
#ifdef DEBUG_BMI
	elog(NOTICE,"[buf_extend] END , bytes ==> %u",
		 bytes);
#endif
	return bytes;
}

/*
 * Spill some HRL compressed tids to disk
 */

static uint16
buf_free_mem(Relation rel, BMTIDBuffer *buf, BlockNumber lov_block, 
		 OffsetNumber off, bool use_wal,
		 bool flush_hot_buffer)
{
	Buffer lovbuf;
	uint16 bytes_freed=0;

#ifdef DEBUG_BMI
	  elog(NOTICE,"[buf_free_mem] BEGIN");
#endif

	/* flush hot_buffer to BMTIDBuffer */
	if (flush_hot_buffer)
	  bytes_freed += hot_buffer_flush(rel,buf,lov_block,off,use_wal,true);

	/* already done */
	if (buf->num_cwords == 0)
		return 0;

#ifdef DEBUG_BMI
	elog(NOTICE,"[buf_free_mem] buf->num_cwords != 0");
#endif

	lovbuf = _bitmap_getbuf(rel, lov_block, BM_WRITE);

	_bitmap_write_new_bitmapwords(rel, lovbuf, off, buf, use_wal);

	_bitmap_relbuf(lovbuf);

#ifdef DEBUG_BMI
	_debug_view_2(buf,"[buf_free_mem] END");
#endif
	bytes_freed += _bitmap_free_tidbuf(buf);
#ifdef DEBUG_BMI
	elog(NOTICE,"[buf_free_mem] END , bytes_freed ==> %u", bytes_freed);
#endif
	return bytes_freed;
}

/*
 * Spill some data out of the buffer to free up space.
 */
static void
buf_make_space(Relation rel, BMTidBuildBuf *locbuf, bool use_wal)
{
	ListCell *cell;

	elog(NOTICE, "making space");

	/*
	 * Now, we could just pull the head of lov_blocks but there'd be no
	 * guarantee that we'd free up enough space.
	 */
	foreach(cell, locbuf->lov_blocks)
	{
		int i;
		BMTIDLOVBuffer *lov_buf = (BMTIDLOVBuffer *)lfirst(cell);
		BlockNumber lov_block = lov_buf->lov_block;

		for(i = 0; i < BM_MAX_LOVITEMS_PER_PAGE; i++)
		{
			BMTIDBuffer *buf = (BMTIDBuffer *)lov_buf->bufs[i];
			OffsetNumber off;

			/* return if we've freed enough space */
			if(locbuf->byte_size < (maintenance_work_mem * 1024L))
				return;
			if(!buf || buf->num_cwords == 0)
				continue;

			off = i + 1;
#ifdef DEBUG_BMI
			elog(NOTICE,"invoking buf_free_mem from buf_make_space");
#endif
			locbuf->byte_size -= buf_free_mem(rel, buf, lov_block, off, 
							  use_wal, false);
		}
		if(locbuf->byte_size < (maintenance_work_mem * 1024L))
			return;
	}
}

/*
 * _bitmap_free_tidbuf() -- release the space.
 */
uint16
_bitmap_free_tidbuf(BMTIDBuffer* buf)
{
	uint16 bytes_freed = 0;

	if (buf->last_tids)
		pfree(buf->last_tids);
	if (buf->cwords)
		pfree(buf->cwords);

	bytes_freed = buf->num_cwords * sizeof(BM_WORD) +
		buf->num_cwords * sizeof(uint64);

	buf->num_cwords = 0;
	buf->curword = 0;
	buf->start_wordno = 0;
	/* Paranoia */
	MemSet(buf->hwords, 0, sizeof(BM_WORD) * BM_NUM_OF_HEADER_WORDS);

	return bytes_freed;
}

/*
 * insertsetbit() -- insert a given set bit into a bitmap
 *	specified by lovBuffer.
 *
 * lovBuffer is pinned and locked.
 */
static void
insertsetbit(Relation rel, Buffer lovBuffer, OffsetNumber lovOffset,
			 uint64 tidnum, BMTIDBuffer *buf, bool use_wal)
{
	Page		lovPage = BufferGetPage(lovBuffer);
	BMLOVItem	lovItem = (BMLOVItem) PageGetItem(lovPage, 
								PageGetItemId(lovPage, lovOffset));

	buf->last_compword = lovItem->bm_last_compword;
	buf->last_word = lovItem->bm_last_word;
	buf->is_last_compword_fill = BM_LAST_COMPWORD_IS_FILL(lovItem); 
	buf->start_wordno = 0;
	buf->last_tid = lovItem->bm_last_setbit;
	if (buf->cwords)
	{
		MemSet(buf->cwords, 0,
				buf->num_cwords * sizeof(BM_WORD));
	}
	MemSet(buf->hwords, 0,
		   BM_CALC_H_WORDS(buf->num_cwords) * sizeof(BM_WORD));
	if (buf->last_tids)
		MemSet(buf->last_tids, 0,
				buf->num_cwords * sizeof(uint64));
	buf->curword = 0;

	/*
	 * Usually, tidnum is greater than lovItem->bm_last_setbit.
	 * However, if this is not the case, this should be called while
	 * doing 'vacuum full' or doing insertion after 'vacuum'. In this
	 * case, we try to update this bit in the corresponding bitmap
	 * vector.
	 */
	if (tidnum <= lovItem->bm_last_setbit)
	{
		/*
		 * Scan through the bitmap vector, and update the bit in
		 * tidnum.
		 */
		updatesetbit(rel, lovBuffer, lovOffset, tidnum, use_wal);

		return;
	}

	/*
	 * To insert this new set bit, we also need to add all zeros between
	 * this set bit and last set bit. We construct all new words here.
	 */
	buf_add_tid_with_fill
	  (rel, buf, lovBuffer, lovOffset, tidnum, use_wal);
	
	/*
	 * If there are only updates to the last bitmap complete word and
	 * last bitmap word, we simply needs to update the lov buffer.
	 */
	if (buf->num_cwords == 0)
	{
		START_CRIT_SECTION();

		MarkBufferDirty(lovBuffer);

		lovItem->bm_last_compword = buf->last_compword;
		lovItem->bm_last_word = buf->last_word;
		lovItem->lov_words_header = BM_LAST_COMPWORD_IS_FILL(lovItem);
		lovItem->bm_last_setbit = tidnum;
		lovItem->bm_last_tid_location = tidnum - tidnum % BM_WORD_SIZE;

		if (use_wal)
			_bitmap_log_bitmap_lastwords
				(rel, lovBuffer, lovOffset, lovItem);
		
		END_CRIT_SECTION();
		return;
	}

	/*
	 * Write bitmap words to bitmap pages. When there are no enough
	 * space for all these bitmap words, new bitmap pages are created.
	 */
	_bitmap_write_new_bitmapwords(rel, lovBuffer, lovOffset,
								  buf, use_wal);
}

/*
 * _bitmap_write_alltids() -- write all tids in the given buffer into disk.
 */
void
_bitmap_write_alltids(Relation rel, BMTidBuildBuf *tids, 
					  bool use_wal)
{
	ListCell *cell;

#ifdef DEBUG_BMI
	elog(NOTICE,"[_bitmap_write_alltids] BEGIN");
#endif
	foreach(cell, tids->lov_blocks)
	{
		int i;
		BMTIDLOVBuffer *lov_buf = (BMTIDLOVBuffer *)lfirst(cell);
		BlockNumber lov_block = lov_buf->lov_block;

		for(i = 0; i < BM_MAX_LOVITEMS_PER_PAGE; i++)
		{
			BMTIDBuffer *buf = (BMTIDBuffer *)lov_buf->bufs[i];
			OffsetNumber off;

			if(!buf || buf->num_cwords == 0)
				continue;

			off = i + 1;

			buf_free_mem(rel, buf, lov_block, off, use_wal, true);
			pfree(buf);

			lov_buf->bufs[i] = NULL;
		}
	}
	list_free_deep(tids->lov_blocks);
	tids->lov_blocks = NIL;
	tids->byte_size = 0;
#ifdef DEBUG_BMI
	elog(NOTICE,"[_bitmap_write_alltids] END");
#endif
}

/*
 * build_inserttuple() -- insert a new tuple into the bitmap index
 *	during the bitmap index construction.
 *
 * Each new tuple has an assigned number -- tidnum, called a
 * tid location, which represents the bit location for this tuple in
 * a bitmap vector. To speed up the construction, this function does not
 * write this tid location into its bitmap vector immediately. We maintain
 * a buffer -- BMTidBuildBuf to keep an array of tid locations
 * for each distinct attribute value.
 *
 * If this insertion causes the buffer to overflow, we write tid locations
 * for enough distinct values to disk to accommodate this new tuple.
 */
static void
build_inserttuple(Relation index, uint64 tidnum,
	ItemPointerData ht_ctid,
	Datum *attdata, bool *nulls, BMBuildState *state)
{

	TupleDesc tupDesc = state->bm_tupDesc; /* Tuple descriptor alias */
	BMTidBuildBuf *tidLocsBuffer = state->bm_tidLocsBuffer; /* BM TID buffer alias */

	Buffer metabuf = _bitmap_getbuf(index, BM_METAPAGE, BM_WRITE); /* metapage buffer */

	/* Initialise LOV block and offset to point to the special NULL value of the Bitmap vector */
	BlockNumber lovBlock = BM_LOV_STARTPAGE;
	OffsetNumber lovOffset = 1;

	int attno; /* temporary attribute counter */
	bool allNulls = true; /* all attributes are NULL */

#ifdef DEBUG_BMI
  elog(NOTICE,"[build_inserttuple] BEGIN"
	   "\n\t- tidnum = %llu"
	   "\n\t- ht_ctid = %08x:%04x"
	   "\n\t- attdata = %p"
	   "\n\t- nulls = %p"
	   ,tidnum
	   ,ItemPointerGetBlockNumber(&ht_ctid),ItemPointerGetOffsetNumber(&ht_ctid)
	   ,attdata
	   ,nulls
	   );
#endif

	/* Check if all attributes have value of NULL. */
	for (attno = 0; attno < state->bm_tupDesc->natts; ++attno)
	{
	if (!nulls[attno])
	{
		allNulls = false;
		break;
	}
	}
	
	/*
	 * Not NULL value for the current tuple (at least one of the attribute has a not NULL value)
	 */
	if (!allNulls)
	{
	bool blockNull;
	bool offsetNull;
	bool found;

	/* See if the attributes allow hashing */
	if (state->lovitem_hash)
	{
		BMBuildLovData *lov;

		/* look up the hash to see if we can find the lov data that way */
		Datum *entry = (Datum *)hash_search(state->lovitem_hash,
			(void *)attdata,
			HASH_ENTER, &found);

		if (!found)
		{
		/* Copy the key values in case someone modifies them */
		for(attno = 0; attno < tupDesc->natts; attno++)
		{
			Form_pg_attribute at = tupDesc->attrs[attno];

			entry[attno] = datumCopy(entry[attno], at->attbyval,
			at->attlen);
		}

		/*
		 * If the inserting tuple has a new value, then we create a new
		 * LOV item.
		 */
		create_lovitem(index, metabuf, tidnum, tupDesc, attdata, 
			nulls, state->bm_lov_heap, state->bm_lov_index,
			&lovBlock, &lovOffset, state->use_wal);

		/* Updates the information in the LOV heap entry about the block and the offset */
		lov = (BMBuildLovData *) &(entry[tupDesc->natts]);
		lov->lov_block = lovBlock;
		lov->lov_off = lovOffset;

		}
		else
		{
		/* Get the block and the offset of the LOV heap item */
		lov = (BMBuildLovData *) &(entry[tupDesc->natts]);
		lovBlock = lov->lov_block;
		lovOffset = lov->lov_off;
		}
	}
	else
	{
		/*
		 * Search the btree to find the right bitmap vector to append
		 * this bit. Here, we reset the scan key and call index_rescan.
		 */
		for (attno = 0; attno<tupDesc->natts; attno++)
		{
		ScanKey theScanKey = (ScanKey)(((char*)state->bm_lov_scanKeys) +
			attno * sizeof(ScanKeyData));
		if (nulls[attno])
		{
			theScanKey->sk_flags = SK_ISNULL;
			theScanKey->sk_argument = attdata[attno];
		}
		else
		{
			theScanKey->sk_flags = 0;
			theScanKey->sk_argument = attdata[attno];
		}
		}

		index_rescan(state->bm_lov_scanDesc, state->bm_lov_scanKeys);	

		found = _bitmap_findvalue(state->bm_lov_heap, state->bm_lov_index,
		state->bm_lov_scanKeys, state->bm_lov_scanDesc,
		&lovBlock, &blockNull, &lovOffset, &offsetNull);

		if (!found)
		{
		/*
		 * If the inserting tuple has a new value, then we create a new
		 * LOV item.
		 */
		create_lovitem(index, metabuf, tidnum, tupDesc, attdata, 
			nulls, state->bm_lov_heap, state->bm_lov_index,
			&lovBlock, &lovOffset, state->use_wal);
		}
	}
	}

	buf_add_tid
	  (index, tidLocsBuffer, tidnum, state, lovBlock, lovOffset);
	_bitmap_wrtbuf(metabuf);
#ifdef DEBUG_BMI
	elog(NOTICE,"[build_inserttuple] END");
#endif
}

/*
 * inserttuple() -- insert a new tuple into the bitmap index.
 *
 * This function finds the corresponding bitmap vector associated with
 * the given attribute value, and inserts a set bit into this bitmap
 * vector. Each distinct attribute value is stored as a LOV item, which
 * is stored in a list of LOV pages.
 *
 * If there is no LOV item associated with the given attribute value,
 * a new LOV item is created and appended into the last LOV page.
 *
 * For support the high-cardinality case for attributes to be indexed,
 * we also maintain an auxiliary heap and a btree structure for all
 * the distinct attribute values so that the search for the
 * corresponding bitmap vector can be done faster. The heap
 * contains all attributes to be indexed and 2 more attributes --
 * the block number of the offset number of the block that stores
 * the corresponding LOV item. The b-tree index is on this new heap
 * and the key contains all attributes to be indexed.
 */
static void
inserttuple(Relation rel, Buffer metabuf, uint64 tidnum, 
			ItemPointerData ht_ctid, TupleDesc tupDesc, Datum *attdata, 
			bool *nulls, Relation lovHeap, Relation lovIndex, ScanKey scanKey,
			IndexScanDesc scanDesc, bool use_wal)
{
	BlockNumber		lovBlock;
	OffsetNumber	lovOffset;
	bool			blockNull, offsetNull;
	bool			allNulls = true;
	int				attno;
	Buffer			lovBuffer;

	BMTIDBuffer		buf;
	MemSet(&buf, 0, sizeof(buf));
	buf_extend(&buf);

	/* Check if the values of given attributes are all NULL. */
	for (attno = 0; attno < tupDesc->natts; attno++)
	{
		if (!nulls[attno])
		{
			allNulls = false;
			break;
		}
	}


	/*
	 * if the inserting tuple has the value NULL, then the LOV item is
	 * the first item in the lovBuffer.
	 */
	if (allNulls)
	{
		lovBlock = BM_LOV_STARTPAGE;
		lovOffset = 1;
	}
	else
	{
		bool res;
	   
		/*
		 * XXX: We lock the meta page to guard against a race condition where
		 * by a concurrent writer is inserting the same key as us and they
		 * create_lovitem() between us calling _bitmap_findvalue() and
		 * create_lovitem().
		 *
		 * The problem is, locking the metapage is pretty heavy handed 
		 * because the read routines need a read lock on it. There are a
		 * few other things we could do instead: use a BM insert lock or
		 * wrap the code below in a PG_TRY and try and catch the unique
		 * constraint violation from the btree code.
		 */
		LockBuffer(metabuf, BM_WRITE);
		res = _bitmap_findvalue(lovHeap, lovIndex, scanKey, scanDesc, &lovBlock,
								&blockNull, &lovOffset, &offsetNull);

		if(!res)
		{
			/*
			 * Search through the lov heap and index to find the LOV item which
			 * has the same value as the inserting tuple. If such an item is
			 * not found, then we create a new LOV item, and insert it into the
			 * lov heap and index.
			 */
			create_lovitem(rel, metabuf, tidnum, tupDesc,
						   attdata, nulls, lovHeap, lovIndex,
						   &lovBlock, &lovOffset, use_wal);
		}
		LockBuffer(metabuf, BUFFER_LOCK_UNLOCK);
	}

	/*
	 * Here, we have found the block number and offset number of the
	 * LOV item that points to the bitmap page, to which we will
	 * append the set bit.
	 */
	lovBuffer = _bitmap_getbuf(rel, lovBlock, BM_WRITE);
	insertsetbit(rel, lovBuffer, lovOffset, tidnum, &buf, use_wal);
	_bitmap_relbuf(lovBuffer);

	_bitmap_free_tidbuf(&buf);
}

/*
 * _bitmap_buildinsert() -- insert an index tuple during index creation.
 */

void
_bitmap_buildinsert(Relation index, ItemPointerData ht_ctid, Datum *attdata, 
					bool *nulls, BMBuildState *state)
{
	uint64 tidOffset; /* Tuple ID offset */
#ifdef DEBUG_BMI
	elog(NOTICE,"[_bitmap_buildinsert] BEGIN");
#endif

	Assert(ItemPointerGetOffsetNumber(&ht_ctid) <= BM_MAX_HTUP_PER_PAGE);

	tidOffset = BM_IPTR_TO_INT(&ht_ctid); 

	/* insert a new bit into the corresponding bitmap */
	build_inserttuple
	  (index, tidOffset, ht_ctid, attdata, nulls, state);

#ifdef DEBUG_BMI
	elog(NOTICE,"[_bitmap_buildinsert] END");
#endif
}

/*
 * _bitmap_doinsert() -- insert an index tuple for a given tuple.
 */
void
_bitmap_doinsert(Relation rel, ItemPointerData ht_ctid, Datum *attdata, 
				 bool *nulls)
{
	uint64			tidOffset;
	TupleDesc		tupDesc;
	Buffer			metabuf;
	BMMetaPage		metapage;
	Relation		lovHeap, lovIndex;
	ScanKey			scanKeys;
	IndexScanDesc	scanDesc;
	int				attno;

	tupDesc = RelationGetDescr(rel);
	if (tupDesc->natts <= 0)
		return ;

	Assert(ItemPointerGetOffsetNumber(&ht_ctid) <= BM_MAX_HTUP_PER_PAGE);
	tidOffset = BM_IPTR_TO_INT(&ht_ctid);

	/* insert a new bit into the corresponding bitmap using the HRL scheme */
	metabuf = _bitmap_getbuf(rel, BM_METAPAGE, BM_READ);
	metapage = (BMMetaPage)PageGetContents(BufferGetPage(metabuf));
	_bitmap_open_lov_heapandindex(metapage, &lovHeap, &lovIndex, 
								  RowExclusiveLock);

	LockBuffer(metabuf, BUFFER_LOCK_UNLOCK);

	scanKeys = (ScanKey) palloc0(tupDesc->natts * sizeof(ScanKeyData));

	for (attno = 0; attno < tupDesc->natts; attno++)
	{
		RegProcedure	opfuncid;
		ScanKey			scanKey;
		Oid eq_opr; /* equality operator */

		/* Get the equality operator OID */
		//get_sort_group_operators(tupDesc->attrs[attno]->atttypid, false, true, false, NULL, &eq_opr, NULL);
		//opfuncid = get_opcode(eq_opr);
		//scanKey = (ScanKey) (((char *)scanKeys) + attno * sizeof(ScanKeyData));

		opfuncid = equality_oper_funcid(tupDesc->attrs[attno]->atttypid);
		scanKey = (ScanKey) (((char *)scanKeys) + attno * sizeof(ScanKeyData));

		ScanKeyEntryInitialize(scanKey, SK_ISNULL, attno + 1, 
							   BTEqualStrategyNumber, InvalidOid, opfuncid, 0);

		if (nulls[attno])
		{
			scanKey->sk_flags = SK_ISNULL;
			scanKey->sk_argument = attdata[attno];
		}
		else
		{
			scanKey->sk_flags = 0;
			scanKey->sk_argument = attdata[attno];
		}
	}

	scanDesc = index_beginscan(lovHeap, lovIndex, SnapshotAny, 
							   tupDesc->natts, scanKeys);

	/* insert this new tuple into the bitmap index. */
	inserttuple(rel, metabuf, tidOffset, ht_ctid, tupDesc, attdata, nulls, 
				lovHeap, lovIndex, scanKeys, scanDesc, true);

	index_endscan(scanDesc);
	_bitmap_close_lov_heapandindex(lovHeap, lovIndex, RowExclusiveLock);

	ReleaseBuffer(metabuf);
	pfree(scanKeys);
}

/*
 * Debug helper functions 
 */

void _debug_view_1(BMTidBuildBuf *x, const char *msg) 
{
  ListCell* c;
  int i=0;
  elog(NOTICE,"[_debug_view_BMTidBuildBuf] %s"
	   "\n\tbyte_size = %u"
	   "\n\tmax_lov_block = %u"
	   "\n\t\tlov_blocks:length = %d"
	   ,msg
	   ,x->byte_size
	   ,x->max_lov_block
	   ,list_length(x->lov_blocks)
	   );
  foreach(c,x->lov_blocks) {
	i++;
  elog(NOTICE,"cell %d = %p"
	   ,i,lfirst(c));
  }
}

void _debug_view_2(BMTIDBuffer *x, const char *msg) 
{
  int i;
  elog(NOTICE,"[_debug_view_BMTIDBuffer] %s"
	   "\n\tlast_compword = %04x"
	   "\n\tlast_word = %04x"
	   "\n\tis_last_compword_fill = %d"
	   "\n\tstart_tid = 0x%llx"
	   "\n\tlast_tid = 0x%llx"
	   "\n\tcurword = %d"
	   "\n\tnum_cwords = %d"
	   "\n\tstart_wordno = %d"
	   "\n\thwords = [ %04x %04x %04x %04x ... ]"
	   "\n\tcwords = [ %04x %04x %04x %04x ... ]"
	   "\n\thot_buffer_block = %08lx"
	   "\n\thot_buffer_count = %d"
	   "\n\thot_buffer_last_offset = %d"
	   ,msg
	   ,x->last_compword
	   ,x->last_word
	   ,x->is_last_compword_fill
	   ,x->start_tid
	   ,x->last_tid
	   ,x->curword
	   ,x->num_cwords
	   ,x->start_wordno
	   ,x->hwords[0],x->hwords[1],x->hwords[2],x->hwords[3]
	   ,x->cwords[0],x->cwords[1],x->cwords[2],x->cwords[3]
	   ,(unsigned long)x->hot_buffer_block
	   ,x->hot_buffer_count
	   ,x->hot_buffer_last_offset
	   );
  Assert(BUF_INIT_WORDS==8);
  for (i=0; i < x->num_cwords; i+=8) {
	elog(NOTICE,"last_tids[%03x-%03x] = %08llx %08llx %08llx %08llx %08llx %08llx %08llx %08llx"
	 ,i,i+7
	 ,(x->last_tids)[i]
	 ,(x->last_tids)[i+1]
	 ,(x->last_tids)[i+2]
	 ,(x->last_tids)[i+3]
	 ,(x->last_tids)[i+4]
	 ,(x->last_tids)[i+5]
	 ,(x->last_tids)[i+6]
	 ,(x->last_tids)[i+7]
	 );
  }
}

