/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
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

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef __ATS_GC_CATS
#define __ATS_GC_CATS

/* ****** ****** */

#include <malloc.h>
#include <unistd.h>

#include "ats_types.h"
#include "gc.hats"

extern ats_void_type
atspre_exit_prerrf(ats_int_type code, ats_ptr_type fmt, ...) ;

/* ****** ****** */

static inline
ats_uint_type pow2_ceil(ats_int_type n) {
  --n ;
  n |= n >> 1 ;
  n |= n >> 2 ;
  n |= n >> 4 ;
  n |= n >> 8 ;
  n |= n >> 16 ;
#if (__ATS_WORDSIZE == 64)
  n |= n >> 32 ;
#endif
  ++n ;
  return n ;
}

//

static inline
ats_int_type log2_floor(ats_uint_type n) {
  int c = 0 ;
  while (n >>= 1) { ++c ; }
  return c;
}

static inline
ats_int_type log2_ceil(ats_uint_type n) {
  return log2_floor(pow2_ceil(n)) ;
}

//

static inline
ats_int_type div_ceil(ats_uint_type n, ats_int_type d) {
  return (n + d - 1) / d ;
}

static inline
ats_int_type mod_pow2(ats_uint_type m, ats_int_type n) {
  return m & ((1 << n) - 1) ;
}

/* ****** ****** */

// compute the direction of stack growth
// 1: upward growth and -1: downard growth

static
ats_int_type volatile
stack_direction_get_aux(ats_ptr_type some_ptr) {
  int some_var ;
  if ((ats_ptr_type)&some_var > some_ptr) return 1; else return -1;
}

static
ats_int_type volatile
stack_direction_get() {
  int some_var ;
  return stack_direction_get_aux((ats_ptr_type)&some_var) ;
}

int the_stack_direction ; // initialized in [gc_init]

/* ****** ****** */

typedef unsigned char byte ;
typedef void* freeitm ;

/* ****** ****** */

// compute the stack base

static
ats_ptr_type stack_base_get() {
  long int pagesize ;
  int pagesize_log ;
  void* base ;
  uintptr_t base_ptr ;

  pagesize = sysconf(_SC_PAGESIZE) ;
  pagesize_log = log2_floor(pagesize) ;

  base_ptr = (uintptr_t)&base ;
  if (the_stack_direction > 0) {
    base = (void*)((base_ptr>>pagesize_log)<<pagesize_log) ;
  } else {
    base = (void*)((((base_ptr>>pagesize_log)+1)<<pagesize_log)-sizeof(freeitm)) ;
  }
  return base ;
}

void* the_stack_base ; // initialized in [gc_init]

/* ****** ****** */

ats_void_type gc_init() {
  the_stack_direction = stack_direction_get() ;
  the_stack_base = stack_base_get() ;
  return ;
}

/* ****** ****** */

typedef struct freelst_struct { 
  struct freelst_struct* next ;
} freelst_struct ;

typedef freelst_struct* freelst ;

// free list of blocks
freelst the_freelst_blk = (freelst)0 ;

// free list array
freelst the_freelst_arr[NUMBER_OF_FREELSTS] = { (freelst)0 } ;

fprint_freelst(FILE* out, freelst fai) {
  fprintf(out, "freelst(%p):\n", fai) ;
  while (fai) { fai = fai->next ; fprintf (out, "  %p\n", fai) ; }
  return ;
}

/* ****** ****** */

// gc_markroot
// must register the globals so as to search for pointers

#if (GLOBALS_ENTRY_PAGESIZE <= 0)
#error "GLOBALS_ENTRY_PAGESIZE >= 1 is needed."
#endif

typedef struct {
  freeitm *data ; size_t size ;
} global_root ;

typedef struct globals_entry_struct {
  global_root *roots ;
  struct globals_entry_struct* next ;
} globals_entry ;

typedef struct {
  int position ;
  global_root *roots ;
  globals_entry *rest ;
#ifdef __ATS_MULTITHREAD
  pthread_mutex_t lock ;
#endif
} globals_head ;

/* ****** ****** */

// gc_malloc0 and gc_free0 :
// memory allocation/deallocation outside GC: however, GC
// must register the allocated memory so as to search for
// pointers

#define BLOCK0_PATTERN 0xc5c5c5c5

typedef struct block0_struct {
  size_t size ; // size in bytes
  struct block0_struct* prev ;
  struct block0_struct* next ;
  void* pattern ; // for run-time checking
  byte data[0] ; // pointer to the rest of memory
} block0_struct ;

typedef block0_struct block0 ;
typedef block0_struct* blocklst0 ;

typedef struct {
  block0_struct* head ;
#ifdef __ATS_MULTITHREAD
  pthread_mutex_t lock ;
#endif
#ifdef __ATS_GC_STATS
  size_t number_of_bytes ;
  size_t number_of_blocks ;
#endif
} blocklst0_head ;

/* ****** ****** */

extern void fprint_block0 (FILE* out, block0* p) ;

/* ****** ****** */

// gcats1_malloc and gcats1_free :
// memory allocation/deallocation inside GC

typedef struct block1_struct {
  size_t item_bsz ; // byte size of each free item
  size_t item_wsz ; // word size of each free item
  char item_bin ; // the free list bin number
  int item_tot ; // total number of free items
  int mark_cnt ; // the count of marked free items
  struct block1_struct* next ; // next block
  freeitm* data ; // pointer to the data
  byte mark_bits[0] ; // mark bits
} block1_struct ;

typedef block1_struct block1 ;
typedef block1_struct* blocklst1 ;

//

int the_block1_count = 0 ;
int the_block1_limit = 1 ;
// int the_block1_limit = 128 ;
// int the_block1_limit = 1024 ;
// int the_block1_limit = 2048 ;
int the_block1_limit_max = 8192 ;
block1* the_sweeplst_arr[NUMBER_OF_FREELSTS] = { (blocklst1)0 } ;

//

#define MARK_SET(x, i) \
  do { (x)[(i) / 8] |= (1 << ((i) % 8)) ; } while (0)

#define IS_MARK_SET(x, i) (((x)[(i) / 8] >> ((i) % 8)) & 0x1)

#define MARK_CLEAR(x, i) \
  do { (x)[(i) / 8] &= ~(1 << ((i) % 8)) ; } while (0)

//

#define TOPSEG_TABLE_SIZE (1 << PTR_TOPSEG_SIZE)
#define BOTSEG_TABLE_SIZE (1 << PTR_BOTSEG_SIZE)

#define PTR_TOPSEG_GET(p) ((p) >> (PTR_BOTBLKSEG_SIZE + NBYTE_PER_WORD_LOG))
#define PTR_BOTSEG_GET(p) \
  (((p) >> (PTR_BLKSEG_SIZE + NBYTE_PER_WORD_LOG)) & (BOTSEG_TABLE_SIZE - 1))
#define PTR_BLKSEG_GET(p) (((p) >> NBYTE_PER_WORD_LOG) & (BLOCK_WORDSIZE - 1))

//

typedef struct botseg_table_struct {
  block1* table[BOTSEG_TABLE_SIZE] ;
} botseg_table ;

botseg_table* botseg_table_make() {
  botseg_table* tbl = malloc(sizeof(botseg_table)) ;
  if (!tbl) {
    ats_exit_errmsg(1, "Exit: [botseg_table_make: malloc] failed\n") ;
  }
/*
  fprintf(stderr, "botseg_table_make: tbl = %p\n", tbl);
*/
  memset(tbl, 0, sizeof(botseg_table)) ;
  return tbl ;
}

static botseg_table*
the_topseg_table[TOPSEG_TABLE_SIZE] = { (botseg_table *)0 } ;

/* ****** ****** */

extern void fprint_block1 (FILE* out, block1* p) ;
extern block1* block1_malloc_word_bin(int iwsz, int ibin) ;
extern void block1_insert(block1* p) ;
extern void block1_free(block1* p) ;
extern freelst block1_freelst_link(block1* p) ;
extern void do_collection() ;

static inline
freeitm gcats1_malloc_word_large(ats_int_type iwsz) {
  block1* p ;
/*
  fprintf (stdout, "gcats1_malloc_word_large: iwsz = %i\n", iwsz) ;
*/
  if (the_block1_count >= the_block1_limit) do_collection() ;
  p = block1_malloc_word_bin(iwsz, -1) ; // -1: special ibin
/*
  fprint_block1 (stdout, p) ;
*/
  block1_insert(p) ;
  return p->data ;
}

static inline
freelst freelst_malloc_bin(int ibin) {
  int iwsz ; block1* p ;
  if (ibin >= FREEITM_SIZE_CUTOFF) {
    iwsz = 1 << (ibin-FREEITM_SIZE_CUTOFF+FREEITM_SIZE_CUTOFF_LOG+1) ;
  } else {
    iwsz = ibin + 1 ;
  }
  p = block1_malloc_word_bin(iwsz, ibin) ;
  block1_insert(p) ;
  return block1_freelst_link(p) ;
}

static inline
freelst freelst_get_bin(int ibin) {
  block1* p ;
  p = the_sweeplst_arr[ibin] ;
  if (!p) {
    if (the_block1_count >= the_block1_limit) do_collection() ;
    p = the_sweeplst_arr[ibin];
    if (!p) {
      return freelst_malloc_bin(ibin) ;
    }
  }
  the_sweeplst_arr[ibin] = p->next ;
  return block1_freelst_link(p) ;
}
					     
freeitm gcats1_malloc(ats_int_type ibsz) {
  int iwsz, ibin ;  freelst fai ;
  iwsz = (ibsz + NBYTE_PER_WORD - 1) >> NBYTE_PER_WORD_LOG ;
  if (iwsz >= BLOCK_WORDSIZE) return gcats1_malloc_word_large(iwsz) ;
  if (iwsz <= FREEITM_SIZE_CUTOFF) {
    ibin = iwsz - 1 ;
  } else {
    ibin = log2_ceil(iwsz)+FREEITM_SIZE_CUTOFF-FREEITM_SIZE_CUTOFF_LOG-1 ;
  }
  fai = the_freelst_arr[ibin] ;
  if (!fai) fai = freelst_get_bin(ibin) ;
  the_freelst_arr[ibin] = fai->next ;
  return (freeitm)fai ;
}

freeitm gcats1_calloc(ats_int_type n, ats_int_type sz) {
  int nsz = n * sz ;
  freeitm p = gcats1_malloc(nsz) ;
/*
  fprintf (stdout, "gcats1_calloc: n = %i and sz = %i and nsz = %i\n", n, sz, nsz) ;
  fprintf (stdout, "gcats1_calloc: memset\n") ;
*/
  return memset(p, 0, nsz) ;
}

ats_void_type gcats1_free(freeitm fi) {
  uintptr_t topseg, botseg ;
  botseg_table* tbl ; block1* p ;
  int ibin ;

  topseg = PTR_TOPSEG_GET((uintptr_t)fi) ;
  tbl = the_topseg_table[topseg] ;

  if (!tbl) {
    atspre_exit_prerrf(
      1, "Exit: [gcats1_free(%p)] failed: invalid pointer\n", fi
    ) ;
  }

  botseg = PTR_BOTSEG_GET((uintptr_t)fi) ;
  p = tbl->table[botseg] ;

  if (!p) {
    atspre_exit_prerrf(
      1, "Exit: [gcats1_free(%p)] failed: invalid pointer\n", fi
    ) ;
  }

  ibin = p->item_bin ;

  if (ibin >= 0) { // small freeitm
    ((freelst)fi)->next = the_freelst_arr[ibin] ;
    the_freelst_arr[ibin] = (freelst)fi ;
  } else { // large freeitm
/*
    fprintf(stderr, "gcats1_free: large freeitm: ibin = %i\n", ibin) ;
*/
    block1_free(p) ;
  }

  return ;
}

/* ****** ****** */

#endif /* __ATS_GC_CATS */

/* end of ats_gc.cats */
