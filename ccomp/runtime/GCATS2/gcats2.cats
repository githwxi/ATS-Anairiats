/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi.
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
*/

/* ****** ****** */

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// October 2009

/* ****** ****** */

#include "ats_types.h"
#include "ats_basics.h"

/* ****** ****** */

#ifndef ATS_RUNTIME_GCATS2_CATS
#define ATS_RUNTIME_GCATS2_CATS

/* ****** ****** */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include <setjmp.h> // for [setjmp] in gcmain_run
#include <sys/mman.h> // for [mmap] in chunkpagelst_replenish

#if (_ATS_MULTITHREAD)
#include <pthread.h>
// for counting the number of threads
#include <semaphore.h> // being put into sleep
#include <signal.h>
#endif // end of [_ATS_MULTITHREAD]

/* ****** ****** */

#include "gcats2_c.h"

/* ****** ****** */

typedef unsigned char byte ;
typedef ats_ptr_type topseg_t ;

typedef ats_ptr_type freeitmptr_vt ;
typedef ats_ptr_type freeitmlst_vt ;

typedef ats_ptr_type freepageptr_vt ;
typedef ats_ptr_type freepagelst_vt ;

typedef struct { void *ptr ; size_t wsz ; } ptrsize_t ;

/* ****** ****** */

//
// external malloc/free functions for GCATS2
//

static inline
ats_ptr_type
gcats2_malloc_ext (ats_size_type bsz) {
  void *p ;
/*
  fprintf(stderr, "gcats2_malloc_ext: bsz = %lu\n", bsz) ;
*/
  p = malloc(bsz) ;
  if (!p) {
    perror("malloc") ;
    fprintf(stderr, "exit(ATS/GC): external memory is unavailable.\n") ;
    exit(1) ;
  } /* end of [if] */
  return p ;
} /* end of [gcats2_malloc_ext] */

static inline
ats_void_type
gcats2_free_ext (ats_ptr_type ptr) { free(ptr); return ; }

static inline
ats_ptr_type
gcats2_realloc_ext (
  ats_ptr_type p, ats_size_type bsz
) {
  void *p_new ;
/*
  fprintf(stderr, "gcats2_realloc_ext: p = %p\n", p) ;
  fprintf(stderr, "gcats2_realloc_ext: bsz = %lu\n", bsz) ;
*/
  p_new = realloc(p, bsz) ;
  if (!p_new) {
    perror("realloc") ;
    fprintf(stderr, "exit(ATS/GC): external memory is unavailable.\n") ;
    exit(1) ;
  } /* end of [if] */
  return p_new ;
} /* end of [gcats2_realloc_ext] */

/* ****** ****** */

static inline
ats_ptr_type
gcats2_mmap_ext (
  ats_size_type bsz
) {
  ats_ptr_type p ;
  p = mmap(
    (void*)0 // start
  , bsz
  , (PROT_READ | PROT_WRITE)
  , (MAP_PRIVATE | MAP_ANONYMOUS)
  , 0 // fd is ignored
  , 0 // offset is ignored
  ) ; // end of [mmap]
  if (p == MAP_FAILED) {
    perror("mmap") ;
    fprintf(stderr, "exit(ATS/GC): [gcats2_mmap_ext]: failed.\n") ;
    exit(1) ;
  } // end of [if]
  return p ;
} /* end of [gcats2_mmap_ext] */

static inline
ats_void_type
gcats2_munmap_ext (
  ats_ptr_type p, ats_size_type bsz
) {
  int err ;
  err = munmap(p, bsz) ;
  if (err) {
    perror("munmap") ;
    fprintf(stderr, "exit(ATS/GC): [gcats2_munmap_ext]: failed.\n") ;
    exit(1) ;
  } // end of [if]
  return ;
} /* end of [gcats2_munmap_ext] */

/* ****** ****** */

static inline
ats_bool_type
gcats2_freeitmlst_isnil (ats_ptr_type xs) {
  return (xs == (freeitmlst_vt*)0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
gcats2_freeitmlst_iscons (ats_ptr_type xs) {
  return (xs != (freeitmlst_vt*)0 ? ats_true_bool : ats_false_bool) ;
}

/*
fun freeitmlst_cons {l1,l2:addr}
  (pf: freeitm_t @ l1 | x: ptr l1, xs: freeitmlst_vt l2): freeitmlst_vt l1
// end of [freeitmlst_cons]
*/

static inline
ats_ptr_type
gcats2_freeitmlst_cons
  (ats_ptr_type x, ats_ptr_type xs) { *(freeitmlst_vt*)x = xs ; return x ; }
// end of [gcats2_freeitmlst_cons]

/*
fun freeitmlst_uncons {l:anz}
  (xs: &freeitmlst_vt l >> freeitmlst_vt l_new):<> #[l_new:addr] (freeitm_t @ l | ptr l)
// end of [freeitmlst_uncons]
*/

static inline
ats_ptr_type
gcats2_freeitmlst_uncons
  (ats_ptr_type r_xs) {
  freeitmlst_vt x = *(freeitmlst_vt*)r_xs ; *(freeitmlst_vt*)r_xs = *(freeitmlst_vt*)x ;
  return x ;
} // end of [gcats2_freeitmlst_uncons]

extern
ats_int_type gcats2_freeitmlst_length (ats_ptr_type xs) ;

extern ats_void_type
gcats2_fprint_freeitmlst (ats_ptr_type out, ats_ptr_type xs) ;

/* ****** ****** */

static inline
topseg_t
PTR_TOPSEG_GET (ats_ptr_type p) {
  uintptr_t u = (uintptr_t)p ;
  return (void*)(u >> (PTR_BOTCHKSEG_SIZE + NBYTE_PER_WORD_LOG)) ;
} /* end of [PTR_TOPSEG_GET] */

static inline
ats_int_type
PTR_BOTSEG_GET (ats_ptr_type p) {
  uintptr_t u = (uintptr_t)p ;
  return (u >> (PTR_CHKSEG_SIZE + NBYTE_PER_WORD_LOG)) & BOTSEG_TABLESIZE_MASK ;
} /* end of [PTR_BOTSEG_GET] */

static inline
ats_int_type
PTR_CHKSEG_GET (ats_ptr_type p) {
  uintptr_t u = (uintptr_t)p ;
  return (u >> NBYTE_PER_WORD_LOG) & CHKSEG_TABLESIZE_MASK ;
} /* end of [PTR_CHKSEG_GET] */

#if (__WORDSIZE == 64)
static inline
topseg_t
PTR_TOPSEGHASH_GET (ats_ptr_type p) {
  uintptr_t u = (uintptr_t)p ;
  return (void*)((u >> (PTR_BOTCHKSEG_SIZE + NBYTE_PER_WORD_LOG)) & TOPSEG_HASHTABLESIZE_MASK) ;
} /* end of [PTR_TOPSEGHASH_GET] */
#endif // end of ...

/* ****** ****** */

typedef
struct manmem_struct {
  size_t manmem_wsz ;
  struct manmem_struct *prev ;
  struct manmem_struct *next ;
  void *manmem_data[0] ; // this is done for alignment concern!
} manmem_vt ;

typedef manmem_vt *manmemlst_vt ;

/*
**  implemented in [gcats2_top.dats]
*/
extern manmemlst_vt the_manmemlst ;

/* ****** ****** */

/*
** implemented in [gcats2_top.dats]
*/

extern size_t the_totwsz ;
extern size_t the_totwsz_limit ;
extern size_t the_totwsz_limit_max ;

static inline
ats_bool_type
gcats2_the_totwsz_limit_is_reached () { return
  (the_totwsz >= the_totwsz_limit) ? ats_true_bool : ats_false_bool ;
} /* end of [the_totwsz_limit_is_reached] */

/* ****** ****** */

/*
** implemented in [gcats2_top.dats]
*/
extern
#if (_ATS_MULTITHREAD)
__thread // thread-local storage
#endif // end of [_ATS_MULTITHREAD]
freeitmlst_vt the_freeitmlstarr[FREEITMLST_ARRAYSIZE] ;

/* ****** ****** */

#define NMARKBIT_PER_CHUNK \
   ((CHUNK_WORDSIZE + NBIT_PER_BYTE_MASK) / NBIT_PER_BYTE)

typedef
struct chunk_struct {
  // the word size of each free item: it must be positive
  size_t itmwsz ; // it can be large!
  // itmwsz = 2^itmwsz_log if itmwsz_log >= 0
  // if [itmwsz_log = -1], then the chunk is large (> CHUNK_WORDSIZE)
  int itmwsz_log ;
//
  int itmtot ; // the total number of freeitms
  int mrkcnt ; // the count of marked freeitms
//
  freepageptr_vt chunk_data ; // pointer to the data // multiple of pagesize
//
  struct chunk_struct *sweepnxt ; // the next swept chunk
//
  // bits for marking // 1 bit for 1 item (>= 1 word)
  byte mrkbits[NMARKBIT_PER_CHUNK] ;
} chunk_vt ;

typedef chunk_vt *chunkptr_vt ;
typedef chunk_vt *chunklst_vt ;

/* ****** ****** */

static inline
ats_ptr_type
gcats2_chunk_data_get
  (ats_ptr_type p_chunk) { return ((chunk_vt*)p_chunk)->chunk_data ; }
// end of ...

static inline
ats_void_type
gcats2_chunk_mrkbits_clear
  (ats_ptr_type p_chunk) {
  int itmtot ; // total number of items
  int nmrkbit ; // number of bytes for mark bits
  itmtot = ((chunk_vt*)p_chunk)->itmtot ;
  nmrkbit = (itmtot + NBIT_PER_BYTE_MASK) >> NBIT_PER_BYTE_LOG ;
/*
  fprintf(stderr, "gcats2_chunk_mrkbits_clear: itmtot = %i\n", itmtot) ;
  fprintf(stderr, "gcats2_chunk_mrkbits_clear: nmrkbit = %i\n", nmrkbit) ;
*/
  memset(((chunk_vt*)p_chunk)->mrkbits, 0, nmrkbit) ;
  ((chunk_vt*)p_chunk)->mrkcnt = 0 ;
  return ;
} /* end of [gcats2_chunk_mrkbits_clear] */

/* ****** ****** */

typedef
struct botsegtbl_struct {
#if (__WORDSIZE == 64)
  uintptr_t hashkey ; struct botsegtbl_struct *hashnext ;
#endif
  chunklst_vt headers[BOTSEG_TABLESIZE] ;
} botsegtbl_vt ;

typedef botsegtbl_vt *botsegtblptr_vt ;

/* ****** ****** */

#if (__WORDSIZE == 32)

extern botsegtbl_vt *the_topsegtbl[TOPSEG_TABLESIZE] ;

static inline
ats_ptr_type
gcats2_the_topsegtbl_takeout (topseg_t ofs) {
  return &the_topsegtbl[(uintptr_t)ofs] ; // 0 <= ofs < TOPSEG_TABLESIZE
} // end of ...

#endif // end of [__WORDSIZE == 32]

#if (__WORDSIZE == 64)

extern botsegtbl_vt *the_topsegtbl[TOPSEG_HASHTABLESIZE] ;

static inline
ats_ptr_type
gcats2_the_topsegtbl_takeout (topseg_t ofs) {
  return &the_topsegtbl[((uintptr_t)ofs) & TOPSEG_HASHTABLESIZE_MASK] ;
} // end of ...

#endif // end of [__WORDSIZE == 64]

/* ****** ****** */

#if (__WORDSIZE == 32)

static inline
ats_ptr_type // &chunkptr
gcats2_botsegtblptr1_takeout ( // used in [ptr_isvalid]
  ats_ptr_type p_botsegtbl // p_botsegtbl != 0
, topseg_t ofs_topseg, int ofs_botseg // [ofs_topseg]: not used
) {
  return &(((botsegtbl_vt*)p_botsegtbl)->headers)[ofs_botseg] ;
} /* end of [botsegtblptr_get] */

#endif // end of [__WORDSIZE == 32]

#if (__WORDSIZE == 64)

static inline
ats_ptr_type // &chunkptr
gcats2_botsegtblptr1_takeout ( // used in [ptr_isvalid]
  ats_ptr_type p_botsegtbl // p_botsegtbl != 0
, topseg_t ofs_topseg, int ofs_botseg // [ofs_topseg]: used
) {
  botsegtbl_vt *p = p_botsegtbl ;
  do {
    if (p->hashkey == (uintptr_t)ofs_topseg) return &(p->headers)[ofs_botseg] ;
    p = p->hashnext ;
  } while (p) ;
  return (chunkptr_vt*)0 ;
} /* end of [botsegtblptr_get] */

#endif // end of [__WORDSIZE == 64]

/* ****** ****** */

static inline
ats_int_type
MARKBIT_GET (
  ats_ptr_type x, ats_int_type i
) { return
  (((byte*)x)[i >> NBIT_PER_BYTE_LOG] >> (i & NBIT_PER_BYTE_MASK)) & 0x1 ;
} /* end of [MARKBIT_GET] */

static inline
ats_void_type
MARKBIT_SET (
  ats_ptr_type x, ats_int_type i
) {
  ((byte*)x)[i >> NBIT_PER_BYTE_LOG] |= (0x1 << (i & NBIT_PER_BYTE_MASK)) ;
  return ;
} /* end of [MARKBIT_SET] */

static inline
ats_int_type
MARKBIT_GETSET (
  ats_ptr_type x, ats_int_type i
) {
  byte* p_bits ; int bit ;
  p_bits = &((byte*)x)[i >> NBIT_PER_BYTE_LOG] ;
  bit = (*p_bits >> (i & NBIT_PER_BYTE_MASK)) & 0x1 ;
  if (bit) {
    return 1 ;
  } else {
    *p_bits |= (0x1 << (i & NBIT_PER_BYTE_MASK)) ; return 0 ;
  } // end of [if]
} /* end of [MARKBIT_GETSET] */

static inline
ats_void_type
MARKBIT_CLEAR (
  ats_ptr_type x, ats_int_type i
) {
  ((byte*)x)[i >> NBIT_PER_BYTE_LOG] &= ~(0x1 << (i & NBIT_PER_BYTE_MASK)) ;
  return ;
} /* end of [MARKBIT_CLEAR] */

/* ****** ****** */

#if (_ATS_MULTITHREAD)
extern pthread_spinlock_t the_manmemlst_lock ;
#endif

static inline
ats_void_type
gcats2_the_manmemlst_lock_acquire () {
#if (_ATS_MULTITHREAD)
  int err ;
  err = pthread_spin_lock (&the_manmemlst_lock) ;
  if (err != 0) {
    fprintf(stderr, "exit(ATS/GC): [the_manmemlst_lock_acquire] failed.\n") ; exit(1) ;
  } // end of [if]
#endif // end of [_ATS_MULTITHREAD]
  return ;
} /* end of [gcats2_the_manmemlst_lock_acquire] */

static inline
ats_void_type
gcats2_the_manmemlst_lock_release () {
#if (_ATS_MULTITHREAD)
  int err ;
  err = pthread_spin_lock (&the_manmemlst_lock) ;
  if (err != 0) {
    fprintf(stderr, "exit(ATS/GC): [the_manmemlst_lock_release] failed.\n") ; exit(1) ;
  } // end of [if]
#endif // end of [_ATS_MULTITHREAD]
  return ;
} /* end of [gcats2_the_manmemlst_lock_release] */

/* ****** ****** */

#if (_ATS_MULTITHREAD)
extern pthread_mutex_t the_threadinfolst_lock ;
#endif // end of [_ATS_MULTITHREAD]

static inline
ats_void_type
gcats2_the_threadinfolst_lock_acquire () {
#if (_ATS_MULTITHREAD)
  int err ;
  err = pthread_mutex_lock (&the_threadinfolst_lock) ;
  if (err != 0) {
    fprintf(stderr, "exit(ATS/GC): [the_threadinfolst_lock_acquire]: failed.\n") ;
    exit(1) ;
  } // end of [if]
#endif // end of [_ATS_MULTITHREAD]
  return ;
} /* end of [gcats2_the_threadinfolst_lock_acquire] */

static inline
ats_void_type
gcats2_the_threadinfolst_lock_release () {
#if (_ATS_MULTITHREAD)
  int err ;
  err = pthread_mutex_unlock (&the_threadinfolst_lock) ;
  if (err != 0) {
    fprintf(stderr, "exit(ATS/GC): [the_threadinfolst_lock_release]: failed.\n") ;
    exit(1) ;
  } // end of [if]
#endif // end of [_ATS_MULTITHREAD]
  return ;
} /* end of [gcats2_the_threadinfolst_lock_release] */

/* ****** ****** */

#if (_ATS_MULTITHREAD)
extern pthread_mutex_t the_gcmain_lock ;
#endif // end of [_ATS_MULTITHREAD]

static inline
ats_void_type
gcats2_the_gcmain_lock_acquire () {
#if (_ATS_MULTITHREAD)
  int err ;
  err = pthread_mutex_lock (&the_gcmain_lock) ;
  if (err != 0) {
    fprintf(stderr, "exit(ATS/GC): [the_gcmain_lock_acquire]: failed.\n") ;
    exit(1) ;
  } // end of [if]
#endif // end of [_ATS_MULTITHREAD]
  return ;
} /* end of [gcats2_the_gcmain_lock_acquire] */

static inline
ats_void_type
gcats2_the_gcmain_lock_release () {
#if (_ATS_MULTITHREAD)
  int err ;
  err = pthread_mutex_unlock (&the_gcmain_lock) ;
  if (err != 0) {
    fprintf(stderr, "exit(ATS/GC): [the_gcmain_lock_release]: failed.\n") ;
    exit(1) ;
  }
#endif // end of [_ATS_MULTITHREAD]
  return ;
} /* end of [gcats2_the_gcmain_lock_release] */

/* ****** ****** */

extern ats_ptr_type
gcats2_ptr_isvalid
  (ats_ptr_type ptr, ats_ref_type r_nitm) ;
// end of ...

extern ats_ptr_type
gcats2_chunk_make_norm
  (ats_size_type itmwsz, ats_int_type itmwsz_log) ;
// end of ...

extern ats_void_type
gcats2_chunk_free_norm (ats_ptr_type p_chunk) ;

extern ats_void_type
gcats2_chunk_free_large (ats_ptr_type p_chunk) ;

extern ats_int_type
gcats2_the_markstackpagelst_length () ;

extern ats_void_type
gcats2_the_markstackpagelst_extend (ats_int_type n) ;

extern ats_void_type
gcats2_the_topsegtbl_clear_mrkbits () ;

extern ats_int_type/*overflowed*/
gcats2_the_gcmain_mark () ; // it is called in [gcmain_run]

ats_void_type
gcats2_freeitmlst_mark (ats_ptr_type xs) ;

extern ats_void_type
gcats2_the_freeitmlstarr_unmark () ; // it is called in [gcmain_run]

extern ats_void_type
gcats2_the_topsegtbl_sweeplst_build () ; // it is called in [gcmain_run]

extern ats_void_type gcats2_the_threadinfolst_lock_acquire() ;
extern ats_void_type gcats2_the_threadinfolst_lock_release() ;

extern ats_void_type gcats2_the_threadinfolst_suspend() ;

/* ****** ****** */

extern ats_ptr_type
gcats2_autmem_malloc_bsz (ats_size_type bsz) ;

extern ats_void_type gcats2_autmem_free (ats_ptr_type p_itm) ;

/* ****** ****** */

#endif /* end of [ATS_RUNTIME_GCATS2_CATS] */

/* ****** ****** */

/* end of [gcats2.cats] */
