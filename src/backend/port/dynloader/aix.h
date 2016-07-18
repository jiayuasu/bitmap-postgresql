/*
 * $PostgreSQL: pgsql/src/backend/port/dynloader/aix.h,v 1.13.6.1 2009/04/25 15:54:02 momjian Exp $
 */

#ifndef PORT_PROTOS_H
#define PORT_PROTOS_H

#ifdef HAVE_DLOPEN

#include <dlfcn.h>
#else							/* HAVE_DLOPEN */

#ifdef __cplusplus
extern		"C"
{
#endif

/*
 * Mode flags for the dlopen routine.
 */
#define RTLD_LAZY		1		/* lazy function call binding */
#define RTLD_NOW		2		/* immediate function call binding */
#define RTLD_GLOBAL		0x100	/* allow symbols to be global */

/*
 * To be able to intialize, a library may provide a dl_info structure
 * that contains functions to be called to initialize and terminate.
 */
struct dl_info
{
	void		(*init) (void);
	void		(*fini) (void);
};

#if __STDC__ || defined(_IBMR2)
void	   *dlopen(const char *path, int mode);
void	   *dlsym(void *handle, const char *symbol);
char	   *dlerror(void);
int			dlclose(void *handle);
#else
void	   *dlopen();
void	   *dlsym();
char	   *dlerror();
int			dlclose();
#endif

#ifdef __cplusplus
}
#endif
#endif   /* HAVE_DLOPEN */

#include "utils/dynamic_loader.h"

#define  pg_dlopen(f)	dlopen((f), RTLD_NOW | RTLD_GLOBAL)
#define  pg_dlsym	dlsym
#define  pg_dlclose dlclose
#define  pg_dlerror dlerror

#endif   /* PORT_PROTOS_H */
