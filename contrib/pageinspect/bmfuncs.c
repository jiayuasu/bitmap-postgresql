/*
 * $PostgreSQL: pgsql/contrib/pageinspect/bmfuncs.c,v 1.8 2008/05/17 01:28:19 adunstan Exp $ 
 *
 *
 * bmfuncs.c
 *
 * Copyright (c) 2008 2ndQuadrant Ltd and 2ndQuadrant Italia
 *
 * Authors: Gabriele Bartolini <gabriele.bartolini@2ndquadrant.it>
 *
 * Permission to use, copy, modify, and distribute this software and
 * its documentation for any purpose, without fee, and without a
 * written agreement is hereby granted, provided that the above
 * copyright notice and this paragraph and the following two
 * paragraphs appear in all copies.
 *
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE TO ANY PARTY FOR DIRECT,
 * INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING
 * LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS
 * DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * THE AUTHOR SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS
 * IS" BASIS, AND THE AUTHOR HAS NO OBLIGATIONS TO PROVIDE MAINTENANCE,
 * SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 */

#include "postgres.h"

#include "access/heapam.h"
#include "access/bitmap.h"
#include "catalog/namespace.h"
#include "catalog/pg_type.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "storage/bufmgr.h"
#include "utils/builtins.h"


#ifdef HAVE_LONG_INT_64
#define UINT64_PRINTF "%lu"
#elif defined(HAVE_LONG_LONG_INT_64)
#define UINT64_PRINTF "%llu"
#endif

extern Datum bm_metap(PG_FUNCTION_ARGS);
extern Datum bm_page_headers(PG_FUNCTION_ARGS);
extern Datum bm_lov_page_stats(PG_FUNCTION_ARGS);
extern Datum bm_bmv_page_stats(PG_FUNCTION_ARGS);

#if 0
extern Datum bt_page_items(PG_FUNCTION_ARGS);
#endif

PG_FUNCTION_INFO_V1(bm_metap);
PG_FUNCTION_INFO_V1(bm_page_headers);
PG_FUNCTION_INFO_V1(bm_lov_page_stats);
PG_FUNCTION_INFO_V1(bm_bmv_page_stats);
#if 0
PG_FUNCTION_INFO_V1(bt_page_items);
#endif

#define IS_INDEX(r) ((r)->rd_rel->relkind == RELKIND_INDEX)
#define IS_BITMAP(r) ((r)->rd_rel->relam == BITMAP_AM_OID)

#define CHECK_PAGE_OFFSET_RANGE(pg, offnum) { \
		if ( !(FirstOffsetNumber <= (offnum) && \
						(offnum) <= PageGetMaxOffsetNumber(pg)) ) \
			 elog(ERROR, "page offset number out of range"); }

/* note: BlockNumber is unsigned, hence can't be negative */
#define CHECK_RELATION_BLOCK_RANGE(rel, blkno) { \
		if ( RelationGetNumberOfBlocks(rel) <= (BlockNumber) (blkno) ) \
			 elog(ERROR, "block number %d out of range", blkno); }

/*
 * cross-call data structure for page headers SRF
 */
struct bm_page_headers_args
{
    Relation rel;
    uint32 blockNum;
};

/*-------------------------------------------------------
 * bm_page_headers()
 *
 * Get the page headers of all the pages of the index
 *
 * Usage: SELECT * FROM bm_page_headers('bm_key');
 *-------------------------------------------------------
 */

Datum
bm_page_headers(PG_FUNCTION_ARGS)
{
    text *relname = PG_GETARG_TEXT_P(0);
    FuncCallContext *fctx; /* state information across calls context */
    struct bm_page_headers_args *uargs;
    char* values[7];
    Datum result = 0;

    if (!superuser())
	ereport(ERROR,
	    (errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
	    (errmsg("must be superuser to use pageinspect functions"))));

    /* First call checks */
    if (SRF_IS_FIRSTCALL())
    {
	MemoryContext mctx;
	TupleDesc tupleDesc;
	RangeVar* relrv = makeRangeVarFromNameList(textToQualifiedNameList(relname));
	Relation rel;

	fctx = SRF_FIRSTCALL_INIT();

	rel = relation_openrv(relrv, AccessShareLock);

	mctx = MemoryContextSwitchTo(fctx->multi_call_memory_ctx);

	uargs = palloc(sizeof(struct bm_page_headers_args));

	uargs->rel = rel; /* relation */
	uargs->blockNum = 0; /* first page */

	/* Build a tuple descriptor for our result type */
	if (get_call_result_type(fcinfo, NULL, &tupleDesc) != TYPEFUNC_COMPOSITE)
	    elog(ERROR, "return type must be a row type");

	fctx->attinmeta = TupleDescGetAttInMetadata(tupleDesc);
	fctx->user_fctx = uargs;
	/* Number of page blocks for the relation */
	fctx->max_calls = RelationGetNumberOfBlocks(rel);

	MemoryContextSwitchTo(mctx);
    }

    fctx = SRF_PERCALL_SETUP();
    uargs = fctx->user_fctx;

    if (fctx->call_cntr < fctx->max_calls)
    {
	Buffer buffer;
	HeapTuple tuple;
	Page page;
	PageHeader phdr;
	uint32 page_size;
	uint32 free_size;
	int j = 0;

	if (!IS_INDEX(uargs->rel) || !IS_BITMAP(uargs->rel))
		elog(ERROR, "relation \"%s\" is not a bitmap index",
			 RelationGetRelationName(uargs->rel));

	CHECK_RELATION_BLOCK_RANGE(uargs->rel, uargs->blockNum);

	/* Read the page */
	buffer = ReadBuffer(uargs->rel, uargs->blockNum);

	/* Get the header information */
	page = BufferGetPage(buffer);
	phdr = (PageHeader) page;
	page_size = PageGetPageSize(page);
	free_size = PageGetFreeSpace(page);

	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", uargs->blockNum);
	values[j] = palloc(32);
	if (uargs->blockNum == 0) {
	    snprintf(values[j++], 32, "META");
	}
	else if (page_size == phdr->pd_special) {
	    /* no special area - LOV PAGE */
	    snprintf(values[j++], 32, "LOV");
	}
	else {
	    snprintf(values[j++], 32, "BMV");
	}
	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", page_size);
	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", phdr->pd_lower);
	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", phdr->pd_upper);
	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", phdr->pd_special);
	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", free_size);

	//uargs->blockNum = uargs->blockNum + 1;
	++uargs->blockNum;

	ReleaseBuffer(buffer);

	tuple = BuildTupleFromCStrings(fctx->attinmeta, values);

	result = HeapTupleGetDatum(tuple);

	SRF_RETURN_NEXT(fctx, result);
    }
    else
    {
	relation_close(uargs->rel, AccessShareLock);
	pfree(uargs);
	SRF_RETURN_DONE(fctx);
    }
}

#if 0
/*-------------------------------------------------------
 * bt_page_items()
 *
 * Get IndexTupleData set in a btree page
 *
 * Usage: SELECT * FROM bt_page_items('bm_key', 1);
 *-------------------------------------------------------
 */

/*
 * cross-call data structure for SRF
 */
struct user_args
{
	Page		page;
	OffsetNumber offset;
};

Datum
bt_page_items(PG_FUNCTION_ARGS)
{
	text	   *relname = PG_GETARG_TEXT_P(0);
	uint32		blkno = PG_GETARG_UINT32(1);
	Datum		result;
	char	   *values[6];
	HeapTuple	tuple;
	FuncCallContext *fctx;
	MemoryContext mctx;
	struct user_args *uargs;

	if (!superuser())
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 (errmsg("must be superuser to use pageinspect functions"))));

	if (SRF_IS_FIRSTCALL())
	{
		RangeVar   *relrv;
		Relation	rel;
		Buffer		buffer;
		BTPageOpaque opaque;
		TupleDesc	tupleDesc;

		fctx = SRF_FIRSTCALL_INIT();

		relrv = makeRangeVarFromNameList(textToQualifiedNameList(relname));
		rel = relation_openrv(relrv, AccessShareLock);

		if (!IS_INDEX(rel) || !IS_BTREE(rel))
			elog(ERROR, "relation \"%s\" is not a btree index",
				 RelationGetRelationName(rel));

		if (blkno == 0)
			elog(ERROR, "block 0 is a meta page");

		CHECK_RELATION_BLOCK_RANGE(rel, blkno);

		buffer = ReadBuffer(rel, blkno);

		/*
		 * We copy the page into local storage to avoid holding pin on the
		 * buffer longer than we must, and possibly failing to release it at
		 * all if the calling query doesn't fetch all rows.
		 */
		mctx = MemoryContextSwitchTo(fctx->multi_call_memory_ctx);

		uargs = palloc(sizeof(struct user_args));

		uargs->page = palloc(BLCKSZ);
		memcpy(uargs->page, BufferGetPage(buffer), BLCKSZ);

		ReleaseBuffer(buffer);
		relation_close(rel, AccessShareLock);

		uargs->offset = FirstOffsetNumber;

		opaque = (BTPageOpaque) PageGetSpecialPointer(uargs->page);

		if (P_ISDELETED(opaque))
			elog(NOTICE, "page is deleted");

		fctx->max_calls = PageGetMaxOffsetNumber(uargs->page);

		/* Build a tuple descriptor for our result type */
		if (get_call_result_type(fcinfo, NULL, &tupleDesc) != TYPEFUNC_COMPOSITE)
			elog(ERROR, "return type must be a row type");

		fctx->attinmeta = TupleDescGetAttInMetadata(tupleDesc);

		fctx->user_fctx = uargs;

		MemoryContextSwitchTo(mctx);
	}

	fctx = SRF_PERCALL_SETUP();
	uargs = fctx->user_fctx;

	if (fctx->call_cntr < fctx->max_calls)
	{
		ItemId		id;
		IndexTuple	itup;
		int			j;
		int			off;
		int			dlen;
		char	   *dump;
		char	   *ptr;

		id = PageGetItemId(uargs->page, uargs->offset);

		if (!ItemIdIsValid(id))
			elog(ERROR, "invalid ItemId");

		itup = (IndexTuple) PageGetItem(uargs->page, id);

		j = 0;
		values[j] = palloc(32);
		snprintf(values[j++], 32, "%d", uargs->offset);
		values[j] = palloc(32);
		snprintf(values[j++], 32, "(%u,%u)",
				 BlockIdGetBlockNumber(&(itup->t_tid.ip_blkid)),
				 itup->t_tid.ip_posid);
		values[j] = palloc(32);
		snprintf(values[j++], 32, "%d", (int) IndexTupleSize(itup));
		values[j] = palloc(32);
		snprintf(values[j++], 32, "%c", IndexTupleHasNulls(itup) ? 't' : 'f');
		values[j] = palloc(32);
		snprintf(values[j++], 32, "%c", IndexTupleHasVarwidths(itup) ? 't' : 'f');

		ptr = (char *) itup + IndexInfoFindDataOffset(itup->t_info);
		dlen = IndexTupleSize(itup) - IndexInfoFindDataOffset(itup->t_info);
		dump = palloc0(dlen * 3 + 1);
		values[j] = dump;
		for (off = 0; off < dlen; off++)
		{
			if (off > 0)
				*dump++ = ' ';
			sprintf(dump, "%02x", *(ptr + off) & 0xff);
			dump += 2;
		}

		tuple = BuildTupleFromCStrings(fctx->attinmeta, values);
		result = HeapTupleGetDatum(tuple);

		uargs->offset = uargs->offset + 1;

		SRF_RETURN_NEXT(fctx, result);
	}
	else
	{
		pfree(uargs->page);
		pfree(uargs);
		SRF_RETURN_DONE(fctx);
	}
}

#endif

/* ------------------------------------------------
 * bm_metap()
 *
 * Get a bitmap index's meta-page information
 *
 * Usage: SELECT * FROM bm_metap('t1_bmkey')
 * ------------------------------------------------
 */
Datum
bm_metap(PG_FUNCTION_ARGS)
{
	text *relname = PG_GETARG_TEXT_P(0);
	Datum result;
	Relation rel;
	RangeVar *relrv;
	BMMetaPage metad;
	TupleDesc tupleDesc;
	int j;
	char *values[3];
	Buffer buffer;
	Page page;
	HeapTuple tuple;

	if (!superuser())
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 (errmsg("must be superuser to use pageinspect functions"))));

	relrv = makeRangeVarFromNameList(textToQualifiedNameList(relname));
	rel = relation_openrv(relrv, AccessShareLock);

	if (!IS_INDEX(rel) || !IS_BITMAP(rel))
		elog(ERROR, "relation \"%s\" is not a bitmap index",
			 RelationGetRelationName(rel));

	/* Get the meta page */
	buffer = ReadBuffer(rel, BM_METAPAGE);
	page = BufferGetPage(buffer);
	metad = (BMMetaPage) PageGetContents(page);

	/* Build a tuple descriptor for our result type */
	if (get_call_result_type(fcinfo, NULL, &tupleDesc) != TYPEFUNC_COMPOSITE)
		elog(ERROR, "return type must be a row type");

	j = 0;
	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", metad->bm_lov_heapId);
	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", metad->bm_lov_indexId);
	values[j] = palloc(32);
	snprintf(values[j++], 32, "%d", metad->bm_lov_lastpage);

	tuple = BuildTupleFromCStrings(TupleDescGetAttInMetadata(tupleDesc),
								   values);
	result = HeapTupleGetDatum(tuple);

	ReleaseBuffer(buffer);

	relation_close(rel, AccessShareLock);

	PG_RETURN_DATUM(result);
}

/* ------------------------------------------------
 * structure for statistics regarding a single LOV page
 * ------------------------------------------------
 */
typedef struct BMLOVPageStat
{
    uint32 blkno;
    uint32 page_size;
    uint32 free_size;
    uint32 max_avail;

    uint32 live_items;
    uint32 dead_items;
    uint32 avg_item_size;
} BMLOVPageStat;

/* -----------------------------------------------
 * bm_lov_page_stats()
 *
 * Usage: SELECT * FROM bm_lov_page_stats('bm_key');
 * -----------------------------------------------
 */
Datum
bm_lov_page_stats(PG_FUNCTION_ARGS)
{
    text *relname = PG_GETARG_TEXT_P(0);
    uint32 blkno = PG_GETARG_UINT32(1);
    Relation rel;
    RangeVar *relrv;
    Buffer buffer; /* buffer for the requested page */
    Page page;
    PageHeader phdr;

    BMLOVPageStat stat;
    char* values[7]; /* returned values (temporary string) */
    HeapTuple tuple; /* Returned tuple */
    TupleDesc tupleDesc; /* Description of the returned tuple */
    int j = 0; /* field counter */
    Datum result; /* result of the function */
    int item_size = 0;
    OffsetNumber maxoff = FirstOffsetNumber;
    OffsetNumber off = FirstOffsetNumber;

    if (!superuser())
	ereport(ERROR,
	    (errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
	    (errmsg("must be superuser to use pageinspect functions"))));

    relrv = makeRangeVarFromNameList(textToQualifiedNameList(relname));
    rel = relation_openrv(relrv, AccessShareLock);

    if (!IS_INDEX(rel) || !IS_BITMAP(rel))
	elog(ERROR, "relation \"%s\" is not a bitmap index",
	     RelationGetRelationName(rel));

    if (blkno == BM_METAPAGE)
	elog(ERROR, "block %d is a meta page", BM_METAPAGE);

    CHECK_RELATION_BLOCK_RANGE(rel, blkno);

    buffer = ReadBuffer(rel, blkno);
    page = BufferGetPage(buffer);
    phdr = (PageHeader) page;

    /* Initialise the data to be returned */
    stat.blkno = blkno;
    stat.page_size = PageGetPageSize(page);
    stat.free_size = PageGetFreeSpace(page);
    stat.max_avail = stat.live_items = stat.dead_items = stat.avg_item_size = 0;

    /* Check the page type */
    if (phdr->pd_special != stat.page_size)
	elog(ERROR, "block %d is a not a LOV page", blkno);

    /* Get the information */
    maxoff = PageGetMaxOffsetNumber(page);

    /* count live and dead tuples, and free space */
    for (off = FirstOffsetNumber; off <= maxoff; ++off)
    {
	ItemId id = PageGetItemId(page, off);
	IndexTuple itup = (IndexTuple) PageGetItem(page, id);

	item_size += IndexTupleSize(itup);

	if (!ItemIdIsDead(id))
	    stat.live_items++;
	else
	    stat.dead_items++;
    }

    if ((stat.live_items + stat.dead_items) > 0)
	stat.avg_item_size = item_size / (stat.live_items + stat.dead_items);

    /* Build a tuple descriptor for our result type */
    if (get_call_result_type(fcinfo, NULL, &tupleDesc) != TYPEFUNC_COMPOSITE)
	elog(ERROR, "return type must be a row type");

    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.blkno);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.page_size);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.free_size);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.max_avail);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.live_items);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.dead_items);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.avg_item_size);

    tuple = BuildTupleFromCStrings(TupleDescGetAttInMetadata(tupleDesc), values);

    result = HeapTupleGetDatum(tuple);

    ReleaseBuffer(buffer);

    relation_close(rel, AccessShareLock);

    PG_RETURN_DATUM(result);
}

/* ------------------------------------------------
 * structure for statistics regarding a single bitmap page
 * ------------------------------------------------
 */
typedef struct BMBMVPageStat
{
    uint32 blkno;
    uint32 page_size;
    uint32 free_size;

    /* opaque data */
    uint16          bm_hrl_words_used;      /* the number of words used */
    BlockNumber     bm_bitmap_next;         /* the next page for this bitmap */
    uint64          bm_last_tid_location; /* the tid location for the last bit in this page */ 
    uint16          bm_page_id; /* bitmap index identifier */

} BMBMVPageStat;

/* -----------------------------------------------
 * bm_bmv_page_stats()
 *
 * Usage: SELECT * FROM bm_bmv_page_stats('bm_key');
 * -----------------------------------------------
 */
Datum
bm_bmv_page_stats(PG_FUNCTION_ARGS)
{
    text *relname = PG_GETARG_TEXT_P(0);
    uint32 blkno = PG_GETARG_UINT32(1);
    Relation rel;
    RangeVar *relrv;
    Buffer buffer; /* buffer for the requested page */
    Page page;
    PageHeader phdr;
    BMPageOpaque opaque = 0;

    BMBMVPageStat stat;
    char* values[7]; /* returned values (temporary string) */
    HeapTuple tuple; /* Returned tuple */
    TupleDesc tupleDesc; /* Description of the returned tuple */
    int j = 0; /* field counter */
    Datum result; /* result of the function */

    if (!superuser())
	ereport(ERROR,
	    (errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
	    (errmsg("must be superuser to use pageinspect functions"))));

    relrv = makeRangeVarFromNameList(textToQualifiedNameList(relname));
    rel = relation_openrv(relrv, AccessShareLock);

    if (!IS_INDEX(rel) || !IS_BITMAP(rel))
	elog(ERROR, "relation \"%s\" is not a bitmap index",
	     RelationGetRelationName(rel));

    if (blkno == BM_METAPAGE)
	elog(ERROR, "block %d is a meta page", BM_METAPAGE);

    CHECK_RELATION_BLOCK_RANGE(rel, blkno);

    buffer = ReadBuffer(rel, blkno);
    page = BufferGetPage(buffer);
    phdr = (PageHeader) page;
    opaque = (BMPageOpaque) PageGetSpecialPointer(page);

    /* Initialise the data to be returned */
    stat.blkno = blkno;
    stat.page_size = PageGetPageSize(page);
    stat.free_size = PageGetFreeSpace(page);

    /* Check the page type */
    if (phdr->pd_special == stat.page_size)
	elog(ERROR, "block %d is a not a BMV page", blkno);

    stat.bm_hrl_words_used = opaque->bm_hrl_words_used; /* the number of words used */
    stat.bm_bitmap_next = opaque->bm_bitmap_next; /* the next page for this bitmap */
    stat.bm_last_tid_location = opaque->bm_last_tid_location; /* the tid location for the last bit in this page */ 
    stat.bm_page_id = opaque->bm_page_id; /* bitmap index identifier */

    /* Build a tuple descriptor for our result type */
    if (get_call_result_type(fcinfo, NULL, &tupleDesc) != TYPEFUNC_COMPOSITE)
	elog(ERROR, "return type must be a row type");

    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.blkno);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.page_size);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.free_size);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.bm_hrl_words_used);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.bm_bitmap_next);
    values[j] = palloc(32);
    snprintf(values[j++], 32, UINT64_PRINTF, stat.bm_last_tid_location);
    values[j] = palloc(32);
    snprintf(values[j++], 32, "%d", stat.bm_page_id);

    tuple = BuildTupleFromCStrings(TupleDescGetAttInMetadata(tupleDesc), values);

    result = HeapTupleGetDatum(tuple);

    ReleaseBuffer(buffer);

    relation_close(rel, AccessShareLock);

    PG_RETURN_DATUM(result);
}

