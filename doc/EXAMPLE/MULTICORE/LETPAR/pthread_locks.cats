/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi.
 *
 * ATS is  free software;  you can redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/*
 * A linker error is issued if a user does not define multithread and
 * tries to use them anyways
 */

#ifndef _LIBC_PTHREAD_LOCKS_CATS
#define _LIBC_PTHREAD_LOCKS_CATS

#ifdef ATS_MULTITHREAD

/*

#define THREAD_SAFE

*/

#include <pthread.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

//

#include "ats_basics.h"

/* ****** ****** */

// locks and tickets for uploading

typedef struct {
  pthread_mutex_t mutex_res; /* for resources */
  pthread_cond_t cond_cnt; /* conditional variable for count == 0 */
  int count;
} uplock_t ; /* linear lock */

typedef uplock_t upticket_t ;

/* ****** ****** */

static inline
ats_void_type
atslib_pthread_uplockopt_unnone (ats_ptr_type p) {
  return ;
}

static inline
ats_ptr_type
atslib_pthread_uplockopt_unsome (ats_ptr_type p) {
  return p ;
}

static inline
ats_bool_type
atslib_pthread_uplockopt_is_none (ats_ptr_type p) {
  return (p ? ats_false_bool : ats_true_bool) ;
}

static inline
ats_bool_type
atslib_pthread_uplockopt_is_some (ats_ptr_type p) {
  return (p ? ats_true_bool : ats_false_bool) ;
}

/* ****** ****** */

static inline
ats_ptr_type
atslib_pthread_uplock_create () {
  uplock_t *p ;
  p = (uplock_t *)ats_malloc_gc(sizeof (uplock_t)) ;
  p->count = 0 ; /* upticket is not issued yet */
  pthread_mutex_init (&p->mutex_res, NULL) ;
  pthread_cond_init (&p->cond_cnt, NULL) ;
  return p ;
}

/* ****** ****** */

static inline
ats_ptr_type
atslib_pthread_upticket_create (ats_ptr_type p0) {
  uplock_t *p = (uplock_t *)p0 ;
  p->count = 1 ; /* upticket is issued */
  return p ;
}

static inline
ats_void_type
atslib_pthread_upticket_upload_and_destroy (ats_ptr_type p0) {
  upticket_t *p = (upticket_t *)p0 ;
  pthread_mutex_lock (&p->mutex_res) ;
  p->count = 0 ;
  pthread_cond_signal (&p->cond_cnt) ;
  pthread_mutex_unlock (&p->mutex_res) ;
  return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_pthread_uplock_download (ats_ptr_type p0) {
  uplock_t *p = (uplock_t *)p0 ;
  pthread_mutex_lock (&p->mutex_res) ;
  while (p->count > 0) {
    pthread_cond_wait (&p->cond_cnt, &p->mutex_res) ;
  }
  p->count = 0 ;
  pthread_mutex_unlock (&p->mutex_res) ;
  pthread_mutex_destroy (&p->mutex_res) ;
  pthread_cond_destroy (&p->cond_cnt) ;
  ats_free_gc (p) ;
  return ;
}

static inline
ats_ptr_type
atslib_pthread_uplock_download_try (ats_ptr_type p0) {
  uplock_t *p = (uplock_t *)p0 ; int cnt ;
  
  pthread_mutex_lock (&p->mutex_res) ;
  cnt = p->count ;
  pthread_mutex_unlock (&p->mutex_res) ;

  if (!cnt) { // no outstanding upticket
    pthread_mutex_destroy (&p->mutex_res) ;
    pthread_cond_destroy (&p->cond_cnt) ;
    ats_free_gc (p) ;
    return (uplock_t *)0 ;
  } else {
    return p ;
  }
}

/* ****** ****** */

#endif // end of [#ifdef ATS_MULTITHREAD]

#endif // end of [#ifndef _LIBC_PTHREAD_LOCKS_CATS]

/* ****** ****** */

/* end of [pthread_locks.cats] */
