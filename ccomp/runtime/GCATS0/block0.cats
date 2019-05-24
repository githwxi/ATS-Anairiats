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

void fprint_block0 (FILE* out, block0* p) {
  fprintf (out, "block0(%p): \n", p);
  fprintf (out, "  size = %i\n", p->size);
  fprintf (out, "  prev = %p\n", p->prev);
  fprintf (out, "  next = %p\n", p->next);
  fprintf (out, "  data = %p\n", p->data);
}

/* ****** ****** */

blocklst0_head the_blocklst0_head = {
  0
#ifdef __ATS_MULTITHREAD
, PTHREAD_MUTEX_INITIALIZER
#endif
#ifdef __ATS_GC_STATS
, 0 // number_of_bytes
, 0 // number_of_blocks
#endif
} ;

/* ****** ****** */

static inline
ats_ptr_type
block0_malloc_err(ats_int_type n) {
  block0 *p ;
  p = (block0 *)malloc(n+sizeof(block0)) ;
  if (p) { p->size = n ; p->pattern = (void *)BLOCK0_PATTERN ; }
  return p ;
}

static inline
ats_void_type
block0_free(ats_ptr_type p_block) { return free(p_block) ; } 

//

static inline
ats_bool_type
blocklst0_is_beg(ats_ptr_type p) {
  if (!p) return ats_true_bool ;
  return ((blocklst0)p)->prev ? ats_true_bool : ats_false_bool ;
}

static inline
ats_bool_type
blocklst0_is_end(ats_ptr_type p) {
  if (!p) return ats_true_bool ;
  return ((blocklst0)p)->next ? ats_true_bool : ats_false_bool ;
}

//

static inline
ats_ptr_type
blocklst0_next(ats_ptr_type p) {
  return (((blocklst0)p)->next) ;
}

static inline
ats_ptr_type
blocklst0_prev(ats_ptr_type p) {
  return (((blocklst0)p)->prev) ;
}

//

static inline
ats_ptr_type
blocklst0_remove(ats_ptr_type root, ats_ptr_type p) {

  if (((blocklst0)p)->next) {
    (((blocklst0)p)->next)->prev = ((blocklst0)p)->prev ;
  }

  if (((blocklst0)p)->prev) {
    (((blocklst0)p)->prev)->next = ((blocklst0)p)->next ;
  } else {
    *((blocklst0 *)root) = ((blocklst0)p)->next ;
  }

  return p ;
}

//

static inline
ats_void_type
the_blocklst0_get() {
#ifdef __ATS_MULTITHREAD
  pthread_mutex_lock (&the_blocklst0_head.lock) ;
#endif
  return ;
}

static inline
ats_void_type
the_blocklst0_set() {
#ifdef __ATS_MULTITHREAD
  pthread_mutex_lock (&the_blocklst0_head.lock) ;
#endif
  return ;
}

//

static inline
ats_void_type
the_blocklst0_cons(ats_ptr_type x) {

  blocklst0 p = the_blocklst0_head.head ;

  the_blocklst0_get () ;
  ((blocklst0)x)->next = p ;
  ((blocklst0)x)->prev = (blocklst0)0 ;
  if (p) p->prev = (blocklst0)x ;
  the_blocklst0_head.head = (blocklst0)x ;
#ifdef __ATS_GC_STATS
  the_blocklst0_head.number_of_bytes += ((block0 *)x)->size ;
  the_blocklst0_head.number_of_blocks += 1 ;
/*
  printf ("the_blocklst0_head.number_of_bytes = %i\n", the_blocklst0_head.number_of_bytes);
  printf ("the_blocklst0_head.number_of_blocks = %i\n", the_blocklst0_head.number_of_blocks);
*/
#endif
  the_blocklst0_set () ;

  return ;
}

static inline
ats_ptr_type
the_blocklst0_take_err(ats_ptr_type p_data) {
  block0* x ;
  block0* p_block = (block0 *)((char *)p_data-sizeof(block0)) ;

  if (p_block->pattern != (void *)BLOCK0_PATTERN) return (block0 *)0 ;

  the_blocklst0_get () ;
  x = blocklst0_remove (&(the_blocklst0_head.head), p_block) ;
#ifdef __ATS_GC_STATS
  the_blocklst0_head.number_of_bytes -= ((block0 *)x)->size ;
  the_blocklst0_head.number_of_blocks -= 1 ;
/*
  printf ("the_blocklst0_head.number_of_bytes = %i\n", the_blocklst0_head.number_of_bytes);
  printf ("the_blocklst0_head.number_of_blocks = %i\n", the_blocklst0_head.number_of_blocks);
*/
#endif
  the_blocklst0_set () ;
  
  return x;
}

static inline
ats_ptr_type
the_blocklst0_realloc_err(ats_ptr_type p_data, ats_int_type n) { 
  block0* p_block ;

  the_blocklst0_get () ;
  p_block = realloc((char *)p_data-sizeof(block0), n+sizeof(block0)) ;

  if (!p_block) return (ats_ptr_type)0 ;

  if (p_block->prev) { (p_block->prev)->next = p_block ; }
  else { the_blocklst0_head.head = p_block ; }

  if (p_block->next) { (p_block->next)->prev = p_block ; }

#ifdef __ATS_GC_STATS
  the_blocklst0_head.number_of_bytes += (n - p_block->size) ;
  p_block->size = n ;
/*
  printf ("the_blocklst0_head.number_of_bytes: %i\n", the_blocklst0_head.number_of_bytes);
*/
#endif  

  the_blocklst0_set () ;
  return (char *)p_block+sizeof(block0) ;
} 

/* end of blocklst0.cats */
