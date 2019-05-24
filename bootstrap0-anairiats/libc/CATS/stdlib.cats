/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
**
** ATS is  free software;  you can redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATS_LIBC_STDLIB_CATS
#define ATS_LIBC_STDLIB_CATS

/* ****** ****** */

#include <errno.h>
#include <stdlib.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

// implemented in [prelude/CATS/printf.cats]
extern ats_void_type
atspre_exit_prerrf(ats_int_type code, ats_ptr_type fmt, ...) ;

/* ****** ****** */

#define atslib_atoi atoi
#define atslib_atof atof
#define atslib_atol atol
#define atslib_atoll atoll

/* ****** ****** */

static inline
ats_ptr_type
atslib_getenv_opt (ats_ptr_type name) { return getenv(name) ; }

static inline
ats_ptr_type
atslib_getenv_exn (const ats_ptr_type name) {
  char *res = getenv(name) ;
  if (!name) {
    atspre_exit_prerrf (1, "exit(ATS): [getenv(%s)] failed.\n", name) ;
  }
  return res ;
} /* end of [atslib_getenv_exn] */

/* ****** ****** */

static inline
ats_int_type
atslib_setenv_err
  (ats_ptr_type name, ats_ptr_type value, ats_int_type overwrite) {
  return setenv((char*)name, (char*)value, (int)overwrite) ;
} /* end of [atslib_setenv_err] */

static inline
ats_void_type
atslib_setenv_exn
  (ats_ptr_type name, ats_ptr_type value, ats_int_type overwrite) {
  int ret = setenv((char*)name, (char*)value, (int)overwrite) ;
  if (ret != 0) {
    perror ("setenv"); atspre_exit_prerrf (
      1, "exit(ATS): [setenv(%s, %s, %i)] failed.\n", name, value, overwrite
    ) ; // end of [atspre_exit_prerrf]
  } /* end of [if] */
  return ;
} /* end of [atslib_setenv_exn] */

/* ****** ****** */

#define atslib_atexit_err atexit

static inline
ats_void_type
atslib_atexit_exn (ats_ptr_type fcn) {
  int err ;
  err = atexit ((void(*)(void))fcn) ;
  if (err != 0) atspre_exit_prerrf (1, "exit(ATS): [atexit] failed.\n") ;
  return ;
} /* end of [atslib_atexit_exn] */

/* ****** ****** */

#define atslib_system_err system

/* ****** ****** */

#define atslib_mkstemp mkstemp

/* ****** ****** */

static inline
ats_int_type
atslib_bsearch (
  ats_ref_type key,
  ats_ref_type base, ats_size_type nmemb, ats_size_type size,
  ats_fun_ptr_type compar
) {
  void *p ;
  p = bsearch (
    key, base, nmemb, size, (int(*)(const void*, const void*))compar
  ) ; // end of [bsearch]
  if (!p) return -1 ;
  return ((char*)p - (char*)base) / size ;
} /* end of [atslib_bsearch] */

/* ****** ****** */

//
// #define atslib_qsort qsort
//
static inline
ats_void_type
atslib_qsort (
  ats_ref_type base,
  ats_size_type nmemb,
  ats_size_type size,
  ats_ptr_type compar
) {
  qsort(base, nmemb, size, (int(*)(const void*, const void*))compar) ;
  return ;
} /* end of [atslib_qsort] */

/* ****** ****** */

#endif /* ATS_LIBC_STDLIB_CATS */

/* end of [stdlib.cats] */
