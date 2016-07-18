#include "hstore.h"

#include "access/gin.h"

#define KEYFLAG		'K'
#define VALFLAG		'V'
#define NULLFLAG	'N'

PG_FUNCTION_INFO_V1(gin_extract_hstore);
Datum		gin_extract_hstore(PG_FUNCTION_ARGS);

static text *
makeitem(char *str, int len)
{
	text	   *item;

	item = (text *) palloc(VARHDRSZ + len + 1);
	SET_VARSIZE(item, VARHDRSZ + len + 1);

	if (str && len > 0)
		memcpy(VARDATA(item) + 1, str, len);

	return item;
}

Datum
gin_extract_hstore(PG_FUNCTION_ARGS)
{
	HStore	   *hs = PG_GETARG_HS(0);
	int32	   *nentries = (int32 *) PG_GETARG_POINTER(1);
	Datum	   *entries = NULL;

	*nentries = 2 * hs->size;

	if (hs->size > 0)
	{
		HEntry	   *ptr = ARRPTR(hs);
		char	   *words = STRPTR(hs);
		int			i = 0;

		entries = (Datum *) palloc(sizeof(Datum) * 2 * hs->size);

		while (ptr - ARRPTR(hs) < hs->size)
		{
			text	   *item;

			item = makeitem(words + ptr->pos, ptr->keylen);
			*VARDATA(item) = KEYFLAG;
			entries[i++] = PointerGetDatum(item);

			if (ptr->valisnull)
			{
				item = makeitem(NULL, 0);
				*VARDATA(item) = NULLFLAG;

			}
			else
			{
				item = makeitem(words + ptr->pos + ptr->keylen, ptr->vallen);
				*VARDATA(item) = VALFLAG;
			}
			entries[i++] = PointerGetDatum(item);

			ptr++;
		}
	}

	PG_FREE_IF_COPY(hs, 0);
	PG_RETURN_POINTER(entries);
}

PG_FUNCTION_INFO_V1(gin_extract_hstore_query);
Datum		gin_extract_hstore_query(PG_FUNCTION_ARGS);

Datum
gin_extract_hstore_query(PG_FUNCTION_ARGS)
{
	StrategyNumber strategy = PG_GETARG_UINT16(2);

	if (strategy == HStoreContainsStrategyNumber)
	{
		PG_RETURN_DATUM(DirectFunctionCall2(
											gin_extract_hstore,
											PG_GETARG_DATUM(0),
											PG_GETARG_DATUM(1)
											));
	}
	else if (strategy == HStoreExistsStrategyNumber)
	{
		text	   *item,
				   *q = PG_GETARG_TEXT_P(0);
		int32	   *nentries = (int32 *) PG_GETARG_POINTER(1);
		Datum	   *entries = NULL;

		*nentries = 1;
		entries = (Datum *) palloc(sizeof(Datum));

		item = makeitem(VARDATA(q), VARSIZE(q) - VARHDRSZ);
		*VARDATA(item) = KEYFLAG;
		entries[0] = PointerGetDatum(item);

		PG_RETURN_POINTER(entries);
	}
	else
		elog(ERROR, "Unsupported strategy number: %d", strategy);

	PG_RETURN_POINTER(NULL);
}

PG_FUNCTION_INFO_V1(gin_consistent_hstore);
Datum		gin_consistent_hstore(PG_FUNCTION_ARGS);

Datum
gin_consistent_hstore(PG_FUNCTION_ARGS)
{
	StrategyNumber strategy = PG_GETARG_UINT16(1);
	bool		res = true;

	if (strategy == HStoreContainsStrategyNumber)
	{
		bool	   *check = (bool *) PG_GETARG_POINTER(0);
		HStore	   *query = PG_GETARG_HS(2);
		int			i;

		for (i = 0; res && i < 2 * query->size; i++)
			if (check[i] == false)
				res = false;
	}
	else if (strategy == HStoreExistsStrategyNumber)
		res = true;
	else
		elog(ERROR, "Unsupported strategy number: %d", strategy);

	PG_RETURN_BOOL(res);
}
