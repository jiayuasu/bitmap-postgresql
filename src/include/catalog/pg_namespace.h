/*-------------------------------------------------------------------------
 *
 * pg_namespace.h
 *	  definition of the system "namespace" relation (pg_namespace)
 *	  along with the relation's initial contents.
 *
 *
 * Portions Copyright (c) 1996-2008, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * $PostgreSQL: pgsql/src/include/catalog/pg_namespace.h,v 1.23 2008/01/01 19:45:56 momjian Exp $
 *
 * NOTES
 *	  the genbki.sh script reads this file and generates .bki
 *	  information from the DATA() statements.
 *
 *-------------------------------------------------------------------------
 */
#ifndef PG_NAMESPACE_H
#define PG_NAMESPACE_H

/* ----------------
 *		postgres.h contains the system type definitions and the
 *		CATALOG(), BKI_BOOTSTRAP and DATA() sugar words so this file
 *		can be read by both genbki.sh and the C compiler.
 * ----------------
 */

/* ----------------------------------------------------------------
 *		pg_namespace definition.
 *
 *		cpp turns this into typedef struct FormData_pg_namespace
 *
 *	nspname				name of the namespace
 *	nspowner			owner (creator) of the namespace
 *	nspacl				access privilege list
 * ----------------------------------------------------------------
 */
#define NamespaceRelationId  2615

CATALOG(pg_namespace,2615)
{
	NameData	nspname;
	Oid			nspowner;
	aclitem		nspacl[1];		/* VARIABLE LENGTH FIELD */
} FormData_pg_namespace;

/* ----------------
 *		Form_pg_namespace corresponds to a pointer to a tuple with
 *		the format of pg_namespace relation.
 * ----------------
 */
typedef FormData_pg_namespace *Form_pg_namespace;

/* ----------------
 *		compiler constants for pg_namespace
 * ----------------
 */

#define Natts_pg_namespace				3
#define Anum_pg_namespace_nspname		1
#define Anum_pg_namespace_nspowner		2
#define Anum_pg_namespace_nspacl		3


/* ----------------
 * initial contents of pg_namespace
 * ---------------
 */

DATA(insert OID = 11 ( "pg_catalog" PGUID _null_ ));
DESCR("system catalog schema");
#define PG_CATALOG_NAMESPACE 11
DATA(insert OID = 99 ( "pg_toast" PGUID _null_ ));
DESCR("reserved schema for TOAST tables");
#define PG_TOAST_NAMESPACE 99
DATA(insert OID = 2200 ( "public" PGUID _null_ ));
DESCR("standard public schema");
#define PG_PUBLIC_NAMESPACE 2200


DATA(insert OID = 3012  ( "pg_bitmapindex" PGUID _null_ ));
DESCR("Reserved schema for internal relations of bitmap indexes");
#define PG_BITMAPINDEX_NAMESPACE 3012

/*
 * prototypes for functions in pg_namespace.c
 */
extern Oid	NamespaceCreate(const char *nspName, Oid ownerId);

#endif   /* PG_NAMESPACE_H */
