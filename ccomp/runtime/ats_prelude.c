/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
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

#include "config.h"

#include <stdio.h>

#ifdef _ATS_MULTITHREAD
#include <pthread.h>
#endif // end of [_ATS_MULTITHREAD]

/* ****** ****** */

#include "ats_types.h"
#include "ats_basics.h"
#include "ats_memory.h"

/* ****** ****** */
//
// HX: implemented in [prelude/DATS/basics.dats]
//
extern void ats_exit_errmsg (int err, char *msg) ;

/* ****** ****** */

/*
** sizeof(ats_empty_type) == 0
*/
ats_empty_type ats_empty_value ;

/* ****** ****** */
//
// HX: The following variables are used in basics.dats
//
int ats_stdin_view_lock = 1 ;
int ats_stdout_view_lock = 1 ;
int ats_stderr_view_lock = 1 ;

/* ****** ****** */

/*
** the type of [the_ats_exception_stack]
** is given in the file [ats_exception.h]
*/

#ifdef _ATS_MULTITHREAD
ATSthreadlocalstorage() // thread-local storage
#endif // end of [_ATS_MULTITHREAD]
void *the_ats_exception_stack = NULL ;

/* ****** ****** */
//
// HX: some common exceptions
//
ats_exn_type
AssertionExceptionCon = { 10, "AssertionException" } ;
ats_exn_ptr_type AssertionException = &AssertionExceptionCon ;

ats_exn_type
OverflowExceptionCon = { 20, "OverflowException" } ;
ats_exn_ptr_type OverflowException = &OverflowExceptionCon ;

ats_exn_type
DivisionByZeroExceptionCon = { 30, "DivisionByZeroException" } ;
ats_exn_ptr_type DivisionByZeroException = &DivisionByZeroExceptionCon ;

/* ****** ****** */

ats_exn_type
ListSubscriptExceptionCon = { 40, "ListSubscriptException" } ;
ats_exn_ptr_type ListSubscriptException = &ListSubscriptExceptionCon ;
ats_exn_ptr_type
ListSubscriptException_make () { return ListSubscriptException ; }
ats_bool_type
isListSubscriptException (ats_exn_ptr_type exn) {
  return (ListSubscriptException->tag==exn->tag ? ats_true_bool : ats_false_bool) ;
}

ats_exn_type
ArraySubscriptExceptionCon = { 50, "ArraySubscriptException" } ;
ats_exn_ptr_type ArraySubscriptException = &ArraySubscriptExceptionCon ;
ats_exn_ptr_type
ArraySubscriptException_make () { return ArraySubscriptException ; }
ats_bool_type
isArraySubscriptException (ats_exn_ptr_type exn) {
  return (ArraySubscriptException->tag==exn->tag ? ats_true_bool : ats_false_bool) ;
}

/* ****** ****** */
//
// HX: the numbers less than 1024 are all
int ats_exception_con_tag = 1024 ; // reserved for special use

/* ****** ****** */

/*
** function for handling uncaught exceptions
*/

extern void exit (int status) ; // declared in [stdlib.h]

ats_void_type
ats_uncaught_exception_handle (
  const ats_exn_ptr_type exn
) {
  fprintf(stderr,
    "exit(ATS): uncaught exception: %s(%d)\n", exn->name, exn->tag
  ) ; exit(1) ;
  return ; // deadcode
} // end of [ats_uncaught_exception_handle]

/* ****** ****** */

/*
** functions for handling match failures
*/

void
ats_caseof_failure_handle (
  const char *loc // location of the failure
) {
  fprintf(stderr, "exit(ATS): %s: match failure.\n", loc) ; exit(1) ;
  return ; // deadcode
} // end of [ats_caseof_failure_handle]

void
ats_funarg_match_failure_handle (
  const char *loc // location of the failure
) {
  fprintf(stderr, "exit(ATS): %s: funarg match failure.\n", loc) ; exit(1) ;
  return ; // deadcode
} // end of [ats_funarg_match_failure_handle]

/* ****** ****** */

/*
** functions for memory allocation and deallocation
*/
//
#undef _ATS_GCFLAG
//
// no GC
//
#ifdef _ATS_NGC
#define _ATS_GCFLAG 1
#include "ats_prelude_ngc.c"
#endif // end-of-ifdef
//
// GC for ATS
//
#ifdef _ATS_GCATS
#define _ATS_GCFLAG 1
#include "ats_prelude_gcats.c"
#endif // end-of-ifdef
//
// BDW-GC for C/C++
//
#ifdef _ATS_GCBDW
#define _ATS_GCFLAG 1
#include "ats_prelude_gcbdw.c"
#endif // end-of-ifdef

/* ****** ****** */

#ifdef _ATS_GCFLAG
//
// already included
//
#else
//
// NGC is the default
//
#include "ats_prelude_ngc.c"
//
#endif // end-of-ifdef

/* ****** ****** */

#ifdef _ATS_MULTITHREAD

/* ****** ****** */

ats_int_type
ats_pthread_create_detached (
  ats_ptr_type f, ats_ptr_type env, ats_ref_type tid_r
) {
  int ret ;
#ifdef _ATS_NGC
  pthread_attr_t attr;
  pthread_attr_init (&attr);
  pthread_attr_setdetachstate (&attr, PTHREAD_CREATE_DETACHED) ;
  ret = pthread_create ((pthread_t*)tid_r, &attr, f, env) ;
#elif _ATS_GCATS
  ret = gc_pthread_create (1/*detached*/, f, env, tid_r) ;
/*
  fprintf (stderr, "exit(ATS): there is no support for pthreads under GCATS.\n") ;
  exit (1) ;
*/
#elif _ATS_GCBDW
  fprintf (stderr, "exit(ATS): there is no support for pthreads under GCBDW.\n") ;
  exit (1) ;
#else // _ATS_NGC is the default
  pthread_attr_t attr;
  pthread_attr_init (&attr);
  pthread_attr_setdetachstate (&attr, PTHREAD_CREATE_DETACHED) ;
  ret = pthread_create ((pthread_t*)tid_r, &attr, f, env) ;
#endif // end of [#ifdef]
  return ret ;
} // end of [ats_pthread_create_detached]

/* ****** ****** */

ats_void_type
ats_pthread_exit () {
  pthread_exit (NULL) ; // HX: this may cause memory leak if not used properly
} // end of [ats_pthread_exit]

/* ****** ****** */

#endif /* [ifdef _ATS_MULTITHREAD] */

/* ****** ****** */

/* end of [ats_prelude.c] */
