(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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
*)

(* ****** ****** *)

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2009

(* ****** ****** *)

// #include "gcats2_ats.hats"

(* ****** ****** *)

#define ATSOPT_NAMESPACE "gcats2_multithread_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

extern
fun the_threadinfolst_suspend
  (pf: !the_threadinfolst_v | (*none*)):<> void
  = "gcats2_the_threadinfolst_suspend"

(* ****** ****** *)

%{^

typedef
struct threadinfo_struct {
  pthread_t pid ;
  void *stackbeg, *stackend ;
  struct threadinfo_struct *prev ;
  struct threadinfo_struct *next ;
  freeitmlst_vt *freeitmlstarr ;
} threadinfo_vt ;

typedef threadinfo_vt *threadinfolst_vt ;
typedef threadinfo_vt *threadinfoptr_vt ;

static int the_nsuspended = 0 ;
static pthread_cond_t
the_nsuspended_iszero = PTHREAD_COND_INITIALIZER ;

threadinfolst_vt the_threadinfolst ;

/*
** this variable possesses the fields: pid, stackbeg, stackend
*/
__thread threadinfo_vt the_threadinfoslf ;

/* ****** ****** */

ats_void_type
gcats2_fprint_the_threadinfoslf_pid
  (ats_ptr_type out) {
  fprintf((FILE*)out, "%i", the_threadinfoslf.pid) ; return ;
} // end of [gcats2_fprint_the_threadinfoslf_pid]

/* ****** ****** */

/*
** implemented in [gcats2_top.dats]
*/
extern sem_t the_gcsleep_semaphore ;

/* ****** ****** */

// [signum] needs to be word-aligned
void SIGUSR1_handle (int signum) {
  void *some_ptr ;
  jmp_buf reg_save ;
  setjmp(reg_save) ;
  asm volatile ("": : :"memory") ;
  sem_post(&the_gcsleep_semaphore) ;
  the_threadinfoslf.stackend = &some_ptr ;
  gcats2_the_threadinfolst_lock_acquire() ;
  the_nsuspended -= 1 ;
  // so [stackend==0] indicates that a thread is not suspended
  the_threadinfoslf.stackend = (void*)0 ;
  if (!the_nsuspended) pthread_cond_signal (&the_nsuspended_iszero) ;
  gcats2_the_threadinfolst_lock_release() ;
  return ;
} /* end of [SIGUSR1_handle] */

void
gcats2_signal_initialize () {
  int err = 0 ;
  struct sigaction action ;
//
  action.sa_handler = &SIGUSR1_handle ;
  sigemptyset (&action.sa_mask) ;
  action.sa_flags = SA_RESTART ;
  err = sigaction(SIGUSR1, &action, NULL) ;
  if (err < 0) {
    perror("sigaction") ;
    fprintf(stderr, "exit(ATS/GC): [gcats2_signal_initialize]: failed.\n") ;
    exit(1);
  } // end of [if]
//
#if (GCATS2_DEBUG > 0)
  fprintf(stderr, "[gcats2_signal_initialize] is done successfully.\n") ;
#endif // end of [GCATS2_DEBUG > 0]
//
  return ;
} /* end of [gcats2_signal_initialize] */

/* ****** ****** */

ats_void_type
gcats2_the_threadinfolst_suspend () {
  int nother ; threadinfo_vt *p_info ;
  nother = 0 ; p_info = the_threadinfolst ;
  // [the_threadinfolst_lock] must be held
  while (p_info) {
    if (p_info != &the_threadinfoslf) {
      nother += 1 ; pthread_kill (p_info->pid, SIGUSR1) ;
    } // end of [if]
    p_info = p_info->next ;
  } // end of [while]
  the_nsuspended = nother ;
  while (nother) {
    sem_wait (&the_gcsleep_semaphore) ; nother -= 1 ;
  } // end of [while]
  return ;
} /* end of [gcats2_the_threadinfolst_suspend] */

ats_void_type
gcats2_the_threadinfolst_restart () {
  if (the_nsuspended) { // wait only if there is another thread
    pthread_cond_wait (&the_nsuspended_iszero, &the_threadinfolst_lock) ;
  } // end of [if]
  return ;
} /* end of [gcats2_the_threadinfolst_restart] */

/* ****** ****** */

extern
ats_ptr_type gcats2_mystackbeg_get () ;

void
gcats2_threadinfo_insert () {
  the_threadinfoslf.pid = pthread_self() ;
/*
  fprintf(stderr, "gcats2_threadinfo_insert: pid = %i\n", the_threadinfoslf.pid) ;
*/
  gcats2_mystackbeg_set(gcats2_mystackdir_get()) ;
  the_threadinfoslf.stackbeg = gcats2_mystackbeg_get () ;
  the_threadinfoslf.stackend = (void*)0 ;
  the_threadinfoslf.prev = (threadinfolst_vt)0 ;
  the_threadinfoslf.next = the_threadinfolst ;
  the_threadinfoslf.freeitmlstarr = &the_freeitmlstarr[0] ;

  gcats2_the_threadinfolst_lock_acquire() ;
  the_threadinfolst->prev = &the_threadinfoslf ; the_threadinfolst = &the_threadinfoslf ;
  gcats2_the_threadinfolst_lock_release() ;
  return ;
} /* end of [gcats2_threadinfo_insert] */

void
gcats2_threadinfo_remove () {
  threadinfolst_vt _prev, _next ;
//
  gcats2_the_threadinfolst_lock_acquire () ;
//
  _prev = the_threadinfoslf.prev ;
  _next = the_threadinfoslf.next ;
  if (_next) {
    _next->prev = _prev ;
  }
  if (_prev) {
    _prev->next = _next ;
  } else { // [the_threadinfolst_self] is the first
    the_threadinfolst = _next ;
  }
//
  gcats2_the_threadinfolst_lock_release () ;
//
  return ;
} /* end of [gcats2_threadinfo_remove] */

/* ****** ****** */

ats_int_type
gcats2_threadinfo_mark (
  threadinfo_vt *p_info
) {
  int i, dir ;
  freeitmlst_vt *freeitmlstarr, *_fr, *_to ;
  int overflow = 0 ;

  /* scanning the thread freeitmlst array */

  freeitmlstarr = p_info->freeitmlstarr ;
  for (
    i = 0; i < FREEITMLST_ARRAYSIZE; i += 1
  ) {
    gcats2_freeitmlst_mark (freeitmlstarr[i]) ;
  } /* end of [while] */

  if (!p_info->stackend) {
    fprintf(stderr, "exit(ATS/GC)") ;
    fprintf(stderr, ": [gcats2_threadinfolst_mark_one]: stackend = 0\n") ;
    exit (1) ;
  } // end of [if]
//
  /* scanning the thread stack */
  dir = gcats2_mystackdir_get () ;
  if (dir > 0) {
    _fr = p_info->stackbeg ; _to = p_info->stackend - 1 ;
  } else {
    _to = p_info->stackbeg ; _fr = p_info->stackend + 1 ;
  } // end of [if]
//
  while (_fr <= _to) { overflow += gcats2_ptr_mark (*_fr++) ; }
//
  return overflow ;
} // end of [gcats2_threadinfo_mark]

ats_int_type
gcats2_the_threadinfolst_mark () {
  int overflow = 0 ;
  threadinfo_vt *p_info = the_threadinfolst ;
// /*
  fprintf(stderr, "gcats2_the_threadinfolst_mark: starts\n") ;
// */
  while (p_info) {
    if (p_info != &the_threadinfoslf) {
      overflow += gcats2_threadinfo_mark(p_info) ;
    } // end of [if]
    p_info = p_info->next ;
  } // end of [while]
// /*
  fprintf(stderr, "gcats2_the_threadinfolst_mark: finishes: overflow = %i\n", overflow) ;
// */
  return overflow ;
} /* end of [gcats2_the_threadinfolst_mark] */

/* ****** ****** */

%} // end of [%{^]

/* ****** ****** */

%{^

ats_ptr_type
gcats2_pthread_stubfun (void *data0) {
  void **data ;
  void *(*start_routine)(void*), *arg, *ret ;
  int linclo ;
//
  data = (void**)data0 ;
  start_routine = (void *(*)(void*))(data[0]) ;
  arg = data[1] ;
  linclo = (int)(intptr_t)(data[2]) ;
//
  gcats2_autmem_free (data) ;
//
  gcats2_threadinfo_insert () ;
//
  pthread_cleanup_push (gcats2_threadinfo_remove, (void*)0) ;
  // fprintf (stderr, "gcats2_pthread_stubfun(bef): call to [start_routine]\n") ;
  ret = start_routine(arg) ;
  // fprintf (stderr, "gcats2_pthread_stubfun(aft): call to [start_routine]\n") ;
  if (linclo) gcats2_autmem_free (arg) ; // a linear closure is freed
  pthread_cleanup_pop(1) ; // [1] means pop and execute
//
  return ret ;
} /* end of [gc_pthread_stubfun] */

ats_int_type
gcats2_pthread_create_cloptr (
  ats_clo_ptr_type cloptr
, pthread_t *r_pid, int detached, int linclo
) {
  void **data ;
  pthread_attr_t attr; pthread_t pid ; int ret ;

  data = gcats2_autmem_malloc_bsz(3 * sizeof(void*)) ;
  data[0] = cloptr->closure_fun ;
  data[1] = cloptr ;
  data[2] = (void*)(intptr_t)linclo ;

  if (detached) {
    pthread_attr_init(&attr) ;
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED) ;
    ret = pthread_create(&pid, &attr, &gcats2_pthread_stubfun, data) ;
  } else {
    ret = pthread_create(&pid, 0/*attr*/, &gcats2_pthread_stubfun, data) ;
  } // end of [if]

  if (ret) gcats2_autmem_free (data) ; if (r_pid) *r_pid = pid ;
  return ret ;
} /* end of [gcats2_pthread_create_cloptr] */

%} // end of [%{^]

/* ****** ****** */

(* end of [gcats2_multithread.dats] *)
