/*-------------------------------------------------------------------------
 *
 * bitmap.c
 *	Implementation of the Hybrid Run-Length (HRL) on-disk bitmap index.
 *
 * Copyright (c) 2007, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *	$PostgreSQL$
 *
 * NOTES
 *	This file contains only the public interface routines.
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/genam.h"
#include "access/bitmap.h"
#include "access/xact.h"
#include "catalog/index.h"
#include "miscadmin.h"
#include "nodes/tidbitmap.h"
#include "storage/lmgr.h"
#include "storage/smgr.h"
#include "parser/parse_oper.h"
#include "utils/memutils.h"
#include "storage/bufmgr.h" /* for buffer manager functions */
#include "storage/relfilenode.h"
static void bmbuildCallback(Relation index,	HeapTuple htup, Datum *attdata,
							bool *nulls, bool tupleIsAlive,	void *state);
static void cleanup_pos(BMScanPosition pos);

/*
 * bmbuild() -- Build a new bitmap index.
 */
Datum
bmbuild(PG_FUNCTION_ARGS)
{
    Relation    heap = (Relation) PG_GETARG_POINTER(0);
    Relation    index = (Relation) PG_GETARG_POINTER(1);
    IndexInfo  *indexInfo = (IndexInfo *) PG_GETARG_POINTER(2);
    double      reltuples;
    BMBuildState bmstate;
    IndexBuildResult *result;
    TupleDesc	tupDesc;

    /* We expect this to be called exactly once. */
    if (RelationGetNumberOfBlocks(index) != 0)
	ereport (ERROR,
	    (errcode(ERRCODE_INDEX_CORRUPTED),
	    errmsg("index \"%s\" already contains data",
	    RelationGetRelationName(index))));

    /* Get the index tuple descriptor */
    tupDesc = RelationGetDescr(index);

    /* Initialize the bitmap index by preparing the meta page and inserting the first LOV item */
    _bitmap_init(index, XLogArchivingActive() && !index->rd_istemp);

    /* Initialize the build state. */
    _bitmap_init_buildstate(index, &bmstate);

    /*
     * Do the initial heap scan for the relation and calls the bmbuildCallback callback function
     * for every tuple in the heap, by passing the 'bmstate' structure
     */
#ifdef DEBUG_BMI
    elog(NOTICE,"[bmbuild] IndexBuildHeapScan PRE");
#endif
    reltuples = IndexBuildHeapScan(heap, index, indexInfo,false,bmbuildCallback, (void *)&bmstate);
#ifdef DEBUG_BMI
    elog(NOTICE,"[bmbuild] IndexBuildHeapScan POST");
#endif

    _bitmap_cleanup_buildstate(index, &bmstate); /* clean up the build state */

	/*
	 * fsync the relevant files to disk, unless we're building
	 * a temporary index
	 */
    if (!(XLogArchivingActive() && !index->rd_istemp))
    {
		FlushRelationBuffers(bmstate.bm_lov_heap);
        smgrimmedsync(bmstate.bm_lov_heap->rd_smgr);

		FlushRelationBuffers(bmstate.bm_lov_index);
		smgrimmedsync(bmstate.bm_lov_index->rd_smgr);

		FlushRelationBuffers(index);
		/* FlushRelationBuffers will have opened rd_smgr */
        smgrimmedsync(index->rd_smgr);
    }
	
	/* return statistics */
	result = (IndexBuildResult *) palloc(sizeof(IndexBuildResult));

	result->heap_tuples = reltuples;
	result->index_tuples = bmstate.ituples;

	PG_RETURN_POINTER(result);
}


/*
 * bminsert() -- insert an index tuple into a bitmap index.
 */
Datum
bminsert(PG_FUNCTION_ARGS)
{
	Relation	rel = (Relation) PG_GETARG_POINTER(0);
	Datum		*datum = (Datum *) PG_GETARG_POINTER(1);
	bool		*nulls = (bool *) PG_GETARG_POINTER(2);
	ItemPointer	ht_ctid = (ItemPointer) PG_GETARG_POINTER(3);

	_bitmap_doinsert(rel, *ht_ctid, datum, nulls);

	PG_RETURN_BOOL(true);
}

/*
 * bmgettuple() -- return the next tuple in a scan.
 */
Datum
bmgettuple(PG_FUNCTION_ARGS)
{
	IndexScanDesc scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	ScanDirection dir = (ScanDirection) PG_GETARG_INT32(1);
	BMScanOpaque  so = (BMScanOpaque)scan->opaque;

	bool res;

	/* 
	 * If we have already begun our scan, continue in the same direction.
	 * Otherwise, start up the scan.
	 */
	if (so->bm_currPos && so->cur_pos_valid)
		res = _bitmap_next(scan, dir);
	else
		res = _bitmap_first(scan, dir);

	PG_RETURN_BOOL(res);
}


/*
 * bmgetbitmap() -- gets all matching tuples, and adds them to a bitmap
 */
Datum
bmgetbitmap(PG_FUNCTION_ARGS)
{
	/* We ignore the second argument as we're returning a hash bitmap */
	IndexScanDesc scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	TIDBitmap *tbm = (TIDBitmap *) PG_GETARG_POINTER(1);
	/* BMScanOpaque so = (BMScanOpaque) scan->opaque; */
	int64 ntids = 0;
	ItemPointer heapTid;

	/* Fetch the first page & tuple. */
	if (!_bitmap_first(scan, ForwardScanDirection))
	{
		/* empty scan */
		PG_RETURN_INT64(0);
	}
	/* Save tuple ID, and continue scanning */
	heapTid = &scan->xs_ctup.t_self;
//	tbm_add_tuples(tbm, heapTid, 1);
	ntids++;

	for (;;)
	{
		/* let _bitmap_next do the heavy lifting */
		if (!_bitmap_next(scan, ForwardScanDirection))
			break;

		/* Save tuple ID, and continue scanning */
		heapTid = &(scan->xs_ctup.t_self);
//		tbm_add_tuples(tbm, heapTid, 1);
		ntids++;
	}

	PG_RETURN_INT64(ntids);
}


/*
 * bmbeginscan() -- start a scan on the bitmap index.
 */
Datum
bmbeginscan(PG_FUNCTION_ARGS)
{
	Relation	rel = (Relation) PG_GETARG_POINTER(0);
	int			nkeys = PG_GETARG_INT32(1);
	ScanKey		scankey = (ScanKey) PG_GETARG_POINTER(2);
	IndexScanDesc scan;

	/* get the scan */
	scan = RelationGetIndexScan(rel, nkeys, scankey);

	PG_RETURN_POINTER(scan);
}

/*
 * bmrescan() -- restart a scan on the bitmap index.
 */
Datum
bmrescan(PG_FUNCTION_ARGS)
{
	IndexScanDesc	scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	ScanKey			scankey = (ScanKey) PG_GETARG_POINTER(1);
	BMScanOpaque	so = (BMScanOpaque) scan->opaque;

	/* so will be NULL if we were called via index_rescan() */
	if (so == NULL)
	{
		so = (BMScanOpaque) palloc(sizeof(BMScanOpaqueData));
		so->bm_currPos = NULL;
		so->bm_markPos = NULL;
		so->cur_pos_valid = false;
		so->mark_pos_valid = false;
		scan->opaque = so;
	}

	if (so->bm_currPos != NULL)
	{
		cleanup_pos(so->bm_currPos);
		MemSet(so->bm_currPos, 0, sizeof(BMScanPositionData));
		so->cur_pos_valid = false;
	}

	if (so->bm_markPos != NULL)
	{
		cleanup_pos(so->bm_markPos);
		MemSet(so->bm_markPos, 0, sizeof(BMScanPositionData));
		so->cur_pos_valid = false;
	}
	/* reset the scan key */
	if (scankey && scan->numberOfKeys > 0)
		memmove(scan->keyData, scankey,
				scan->numberOfKeys * sizeof(ScanKeyData));

	PG_RETURN_VOID();
}

/*
 * bmendscan() -- close a scan.
 */
Datum
bmendscan(PG_FUNCTION_ARGS)
{
	IndexScanDesc	scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	BMScanOpaque	so = (BMScanOpaque) scan->opaque;

	/* free the space */
	if (so->bm_currPos != NULL)
	{
		/*
		 * release the buffers that have been stored for each related 
		 * bitmap vector.
		 */
		if (so->bm_currPos->nvec > 1)
			 _bitmap_cleanup_batchwords(so->bm_currPos->bm_batchWords);
		_bitmap_cleanup_scanpos(so->bm_currPos->posvecs,
								so->bm_currPos->nvec);
		so->bm_currPos = NULL;
	}

	if (so->bm_markPos != NULL)
	{
		if (so->bm_markPos->nvec > 1)
			 _bitmap_cleanup_batchwords(so->bm_markPos->bm_batchWords);
		_bitmap_cleanup_scanpos(so->bm_markPos->posvecs,
								so->bm_markPos->nvec);
		so->bm_markPos = NULL;
	}

	pfree(so);
	scan->opaque = NULL;

	PG_RETURN_VOID();
}

/*
 * bmmarkpos() -- save the current scan position.
 */
Datum
bmmarkpos(PG_FUNCTION_ARGS)
{
	IndexScanDesc	scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	BMScanOpaque	so = (BMScanOpaque) scan->opaque;
	BMVector	bmScanPos;
	uint32 vectorNo;

	/* free the space */
	if (so->mark_pos_valid)
	{
		/*
		 * release the buffers that have been stored for each
		 * related bitmap.
		 */
		bmScanPos = so->bm_markPos->posvecs;

		for (vectorNo=0; vectorNo < so->bm_markPos->nvec; vectorNo++)
		{
			if (BufferIsValid((bmScanPos[vectorNo]).bm_lovBuffer))
			{
				ReleaseBuffer((bmScanPos[vectorNo]).bm_lovBuffer);
				(bmScanPos[vectorNo]).bm_lovBuffer = InvalidBuffer;
			}
		}
		so->mark_pos_valid = false;
	}

	if (so->cur_pos_valid)
	{
		uint32	size = sizeof(BMScanPositionData);
		bool need_init = false;

		/* set the mark position */
		if (so->bm_markPos == NULL)
		{
			so->bm_markPos = (BMScanPosition) palloc(size);
			so->bm_markPos->posvecs = 
				(BMVector)palloc0(so->bm_currPos->nvec * sizeof(BMVectorData));
			need_init = true;
		}

		bmScanPos = so->bm_currPos->posvecs;

		for (vectorNo = 0; vectorNo < so->bm_currPos->nvec; vectorNo++)
		{
			BMVector p = &(so->bm_markPos->posvecs[vectorNo]);
			
			if (BufferIsValid((bmScanPos[vectorNo]).bm_lovBuffer))
				IncrBufferRefCount((bmScanPos[vectorNo]).bm_lovBuffer);

			if (need_init)
			{
				p->bm_batchWords = 
					(BMBatchWords *) palloc0(sizeof(BMBatchWords));
				_bitmap_init_batchwords(p->bm_batchWords,
										BM_NUM_OF_HRL_WORDS_PER_PAGE,
										CurrentMemoryContext);
			}
		}

		if (so->bm_currPos->nvec == 1)
		{
			so->bm_markPos->bm_batchWords = 
				so->bm_markPos->posvecs->bm_batchWords;
		}

		memcpy(so->bm_markPos->posvecs, bmScanPos,
			   so->bm_currPos->nvec *
			   sizeof(BMVectorData));
		memcpy(so->bm_markPos, so->bm_currPos, size);

		so->mark_pos_valid = true;
	}

	PG_RETURN_VOID();
}

/*
 * bmrestrpos() -- restore a scan to the last saved position.
 */
Datum
bmrestrpos(PG_FUNCTION_ARGS)
{
	IndexScanDesc	scan = (IndexScanDesc) PG_GETARG_POINTER(0);
	BMScanOpaque	so = (BMScanOpaque) scan->opaque;

	BMVector	bmScanPos;
	uint32 vectorNo;

	/* free space */
	if (so->cur_pos_valid)
	{
		/* release the buffers that have been stored for each related bitmap.*/
		bmScanPos = so->bm_currPos->posvecs;

		for (vectorNo=0; vectorNo<so->bm_markPos->nvec;
			 vectorNo++)
		{
			if (BufferIsValid((bmScanPos[vectorNo]).bm_lovBuffer))
			{
				ReleaseBuffer((bmScanPos[vectorNo]).bm_lovBuffer);
				(bmScanPos[vectorNo]).bm_lovBuffer = InvalidBuffer;
			}
		}
		so->cur_pos_valid = false;
	}

	if (so->mark_pos_valid)
	{
		uint32	size = sizeof(BMScanPositionData);

		/* set the current position */
		if (so->bm_currPos == NULL)
		{
			so->bm_currPos = (BMScanPosition) palloc(size);
		}

		bmScanPos = so->bm_markPos->posvecs;

		for (vectorNo=0; vectorNo<so->bm_currPos->nvec;
			 vectorNo++)
		{
			if (BufferIsValid((bmScanPos[vectorNo]).bm_lovBuffer))
				IncrBufferRefCount((bmScanPos[vectorNo]).bm_lovBuffer);
		}		

		memcpy(so->bm_currPos->posvecs, bmScanPos,
			   so->bm_markPos->nvec *
			   sizeof(BMVectorData));
		memcpy(so->bm_currPos, so->bm_markPos, size);
		so->cur_pos_valid = true;
	}

	PG_RETURN_VOID();
}

/*
 * bmbulkdelete() -- bulk delete index entries
 *
 * Re-index is performed before retrieving the number of tuples
 * indexed in this index.
 */
Datum
bmbulkdelete(PG_FUNCTION_ARGS)
{
	IndexVacuumInfo *info = (IndexVacuumInfo *) PG_GETARG_POINTER(0);
	Relation	rel = info->index;
	IndexBulkDeleteResult * volatile result =
		(IndexBulkDeleteResult *) PG_GETARG_POINTER(1);
	IndexBulkDeleteCallback callback = 
		(IndexBulkDeleteCallback) PG_GETARG_POINTER(2);              
    void       *callback_state = (void *) PG_GETARG_POINTER(3);

	/* allocate stats if first time through, else re-use existing struct */
	if (result == NULL)
		result = (IndexBulkDeleteResult *)
			palloc0(sizeof(IndexBulkDeleteResult));	

	result = (IndexBulkDeleteResult *) palloc0(sizeof(IndexBulkDeleteResult));

	_bitmap_vacuum(info, result, callback, callback_state);
	
	result->num_pages = RelationGetNumberOfBlocks(rel);
	/* Since we re-build the index, set this to number of heap tuples. */
	result->num_index_tuples = info->num_heap_tuples;
	result->tuples_removed = 0;
	
	PG_RETURN_POINTER(result);
}

/*
 * bmvacuumcleanup() -- post-vacuum cleanup.
 *
 * We do nothing useful here.
 */
Datum
bmvacuumcleanup(PG_FUNCTION_ARGS)
{
	IndexVacuumInfo *info = (IndexVacuumInfo *) PG_GETARG_POINTER(0);
	Relation	rel = info->index;
	IndexBulkDeleteResult *stats = 
			(IndexBulkDeleteResult *) PG_GETARG_POINTER(1);

	if(stats == NULL)
		stats = (IndexBulkDeleteResult *)palloc0(sizeof(IndexBulkDeleteResult));

	/* update statistics */
	stats->num_pages = RelationGetNumberOfBlocks(rel);
	stats->pages_deleted = 0;
	stats->pages_free = 0;
	/* XXX: dodgy hack to shutup index_scan() and vacuum_index() */
	stats->num_index_tuples = info->num_heap_tuples;

	PG_RETURN_POINTER(stats);
}

/*
 * Per-tuple callback from IndexBuildHeapScan
 */
static void
bmbuildCallback(Relation index, HeapTuple htup, Datum *attdata,
				bool *nulls, bool tupleIsAlive,	void *state)
{
    BMBuildState *bstate = (BMBuildState *) state;

#ifdef DEBUG_BMI
    elog(NOTICE,"[bmbuildCallback] BEGIN");
#endif

    _bitmap_buildinsert(index, htup->t_self, attdata, nulls, bstate);
    ++bstate->ituples;

#ifdef DEBUG_BMI
    elog(NOTICE,"[bmbuildCallback] END");
#endif
}

/* NOTA: la prossima funzione è stata commentata in quanto probabilmente obsoleta */
#if 0

/*
 * free the memory associated with the stream
 */

static void
stream_free(void *opaque)
{
	IndexStream *is = (IndexStream *)opaque;

	if (is)
	{
		BMStreamOpaque *so = (BMStreamOpaque *)is->opaque;

		if (so)
			pfree(so);
		pfree(is);
	}
}

#endif

static void
cleanup_pos(BMScanPosition pos) 
{
	if (pos->nvec == 0)
		return;
	
	/*
	 * Only cleanup bm_batchWords if we have more than one vector since
	 * _bitmap_cleanup_scanpos() will clean it up for the single vector
	 * case.
	 */
	if (pos->nvec > 1)
		 _bitmap_cleanup_batchwords(pos->bm_batchWords);
	_bitmap_cleanup_scanpos(pos->posvecs, pos->nvec);
}

