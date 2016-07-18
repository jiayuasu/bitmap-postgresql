/*-------------------------------------------------------------------------
 *
 * index.h
 *	  prototypes for catalog/index.c.
 *
 *
 * Portions Copyright (c) 1996-2008, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * $PostgreSQL: pgsql/src/include/catalog/index.h,v 1.75.2.1 2008/11/13 17:42:19 tgl Exp $
 *
 *-------------------------------------------------------------------------
 */
#ifndef INDEX_H
#define INDEX_H

#include "nodes/execnodes.h"


#define DEFAULT_INDEX_TYPE	"btree"

/* Typedef for callback function for IndexBuildHeapScan */
typedef void (*IndexBuildCallback) (Relation index,
												HeapTuple htup,
												Datum *values,
												bool *isnull,
												bool tupleIsAlive,
												void *state);

/* Action code for index_set_state_flags */
typedef enum
{
	INDEX_CREATE_SET_READY,
	INDEX_CREATE_SET_VALID
} IndexStateFlagsAction;


extern Oid index_create(Oid heapRelationId,
			 const char *indexRelationName,
			 Oid indexRelationId,
			 IndexInfo *indexInfo,
			 Oid accessMethodObjectId,
			 Oid tableSpaceId,
			 Oid *classObjectId,
			 int16 *coloptions,
			 Datum reloptions,
			 bool isprimary,
			 bool isconstraint,
			 bool allow_system_table_mods,
			 bool skip_build,
			 bool concurrent);

extern void index_drop(Oid indexId);

extern IndexInfo *BuildIndexInfo(Relation index);

extern void FormIndexDatum(IndexInfo *indexInfo,
			   TupleTableSlot *slot,
			   EState *estate,
			   Datum *values,
			   bool *isnull);

extern void setNewRelfilenode(Relation relation, TransactionId freezeXid);

extern void index_build(Relation heapRelation,
			Relation indexRelation,
			IndexInfo *indexInfo,
			bool isprimary,
			bool isreindex);

extern double IndexBuildHeapScan(Relation heapRelation,
				   Relation indexRelation,
				   IndexInfo *indexInfo,
				   bool allow_sync,
				   IndexBuildCallback callback,
				   void *callback_state);

extern void validate_index(Oid heapId, Oid indexId, Snapshot snapshot);

extern void index_set_state_flags(Oid indexId, IndexStateFlagsAction action);

extern void reindex_index(Oid indexId);
extern bool reindex_relation(Oid relid, bool toast_too);

#endif   /* INDEX_H */
