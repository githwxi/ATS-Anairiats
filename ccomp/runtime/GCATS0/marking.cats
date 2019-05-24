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

// functions for marking 

typedef struct { size_t size ; freeitm data ; } markstack_entry ;

typedef struct markstack_page_struct {
  struct markstack_page_struct* next ;
  struct markstack_page_struct* prev ;
  markstack_entry* entries ;
} markstack_page ;

markstack_page* the_markstack_page0 = (markstack_page *)0 ; // the head page
markstack_page* the_markstack_page ; // the current one
markstack_entry* the_markstack_entry ;
int the_markstack_position ;

void markstack_init() {
  if (!the_markstack_page0) {
    the_markstack_page0 = malloc (sizeof(markstack_page)) ;
    if (!the_markstack_page0) { 
      ats_exit_errmsg(1, "Exit: [markstack_init: malloc] failed.\n") ;
    }
    the_markstack_page0->next = (markstack_page *)0 ;
    the_markstack_page0->prev = (markstack_page *)0 ;
    the_markstack_page0->entries =
      malloc((MAX_MARKSTACK_POSITION+1) * sizeof(markstack_entry)) ;
    if (!the_markstack_page0->entries) { 
      ats_exit_errmsg(1, "Exit: [markstack_init: malloc] failed.\n") ;
    }
    the_markstack_page = the_markstack_page0 ;
    the_markstack_entry = the_markstack_page0->entries ;
    the_markstack_position = 0 ;
  }
  return ;
}


static inline
void markstack_pop(freeitm* data, size_t* size) {
  if (the_markstack_position > 0) {
    --the_markstack_position ;
    --the_markstack_entry ;
    *data = the_markstack_entry->data;
    *size = the_markstack_entry->size;
    return ;
  }
  if (!the_markstack_page->prev) { *data = (freeitm)0 ; return ; }
  the_markstack_page = the_markstack_page->prev ;
  the_markstack_position = MAX_MARKSTACK_POSITION ;
  the_markstack_entry = the_markstack_page->entries + MAX_MARKSTACK_POSITION ;
  *data = the_markstack_entry->data;
  *size = the_markstack_entry->size;
  return ;
}

static inline
void markstack_push(freeitm data, size_t size) {
  markstack_page *page_new ;

  the_markstack_entry->data = data ;
  the_markstack_entry->size = size ;
  
  if (the_markstack_position < MAX_MARKSTACK_POSITION) {
    ++the_markstack_position ;
    ++the_markstack_entry ;
    return ;
  }

  if (the_markstack_page->next) {
    the_markstack_page = the_markstack_page->next ;
    the_markstack_position = 0 ;
    the_markstack_entry = the_markstack_page->entries ;
    return ;
  }

  page_new = malloc(sizeof(markstack_page)) ;
  if (!page_new) { 
    ats_exit_errmsg(1, "Exit: [markstack_push: malloc] failed.\n") ;
  }
  
  page_new->next = (markstack_page *)0 ;
  page_new->prev = the_markstack_page ;
  the_markstack_page = page_new ;

  the_markstack_entry = malloc((MAX_MARKSTACK_POSITION+1) * sizeof(markstack_entry)) ;
  if (!the_markstack_entry) { 
    ats_exit_errmsg(1, "Exit: [markstack_push: malloc] failed.\n") ;
  }

  return ;  
}

//

// The function sets mark bit properly if the given pointer is valid;
// it also returns the block to which the pointer points
static inline
block1* do_markstack_ptr(freeitm fi) {
  uintptr_t topseg, botseg, blkseg ; int offs ;
  botseg_table *tbl ;
  block1 *p ;
  byte* mbs ; // mark bits

  if (!fi) return (block1 *)0 ;
  if ((uintptr_t)fi & (NBYTE_PER_WORD - 1)) return (block1 *)0 ;

  topseg = PTR_TOPSEG_GET((uintptr_t)fi) ;
  tbl = the_topseg_table[topseg] ;
  if (!tbl) { return (block1 *)0 ; }

  botseg = PTR_BOTSEG_GET((uintptr_t)fi) ;
  p = tbl->table[botseg] ;
  if (!p) { return (block1 *)0 ; }

  blkseg = PTR_BLKSEG_GET((uintptr_t)fi) ;
  if (blkseg % p->item_wsz != 0) {
    return (block1 *)0 ;
  }
  offs = blkseg / p->item_wsz ;
/*
  fprintf(stdout, "--do_markstack_ptr:\n") ;
  fprintf(stdout, "topseg = %i and botseg = %i and blkseg = %i\n", topseg, botseg, blkseg) ;
  fprint_block1(stdout, p) ;
*/
  mbs = p->mark_bits ;
  if (IS_MARK_SET(mbs, offs)) return (block1 *)0 ;

  MARK_SET(mbs, offs) ; ++(p->mark_cnt) ;

  return p ;  
}

// This is the main function for marking
void do_markstack_one(freeitm data) {
  int i; size_t size ; block1 *p ; freeitm *datai ;

/*
  fprintf (stdout, "do_markstack_one: data = %p\n", data) ;
*/

  while (1) {
    p = do_markstack_ptr(data) ;
    if (!p) {
      markstack_pop(&data, &size) ; if (!data) break ;
    } else {
      size = p->item_wsz ; // size in words
    }

    if (size > MARKSTACK_CUTOFF) {
      markstack_push(((freeitm *)data)+MARKSTACK_CUTOFF, size-MARKSTACK_CUTOFF) ;
      size = MARKSTACK_CUTOFF ;
    }

    i = 0; datai = (freeitm *)data;
    while (i < size - 1) {
      data = *datai ;
      p = do_markstack_ptr(data) ;
      if (p) { markstack_push(data, p->item_wsz) ; } 
      i += 1 ; ++datai ;
    }
    data = *datai ;
  } // end of while

  return ;
}

//

static do_markstack_globals() {
  int i, j ; globals_entry *rest ; global_root *roots ; freeitm* datai ;

  the_globals_head_get() ;

  roots = the_globals_head.roots ;

  if (!roots) return ; // no globals

  i = the_globals_head.position ; roots += i;

  while (i < GLOBALS_ENTRY_PAGESIZE) {
/*
    fprintf (stdout, "do_markstack_globals: *datai = %p\n", *datai) ;
    fprintf (stdout, "do_markstack_globals: **datai = %p\n", *((freeitm*)(*datai))) ;
*/
    datai = roots->data ;
    for (j = 0; j + sizeof(freeitm) <= roots->size; ++j) {
      do_markstack_one(*datai) ; ++datai ;
    }
    ++i ; ++roots ;
  }

  rest = the_globals_head.rest ;
  while (rest) {
    roots = rest->roots ;
    for (i = 0; i < GLOBALS_ENTRY_PAGESIZE; ++i) {
      datai = roots->data ;
      for (j = 0; j + sizeof(freeitm) <= roots->size; ++j) {
        do_markstack_one(*datai) ; ++datai ;
      }
      ++roots ;
    }
    rest = rest->next ;
  }

  the_globals_head_set() ;

  return ;
}

//

static do_markstack_blocklst0() {
  int i ; blocklst0 p ; freeitm* datai ;

  the_blocklst0_get() ;
  p = the_blocklst0_head.head ;
  while (p) {
/*
    fprintf(stdout, "--do_markstack_blocklst0:\n") ;
    fprint_block0(stdout, p) ;
*/
    datai = (freeitm*)p->data ;
    for (i = 0 ; i < p->size ; i += sizeof(freeitm)) {
      do_markstack_one(*datai) ; ++datai ;
    }
    p = p->next ;
  }
  the_blocklst0_set() ;
}

static do_markstack_stack() {
  freeitm *start, *finish ;

  start = (freeitm *)the_stack_base ; finish = (freeitm *)(&finish) ;

  if (the_stack_direction > 0) { // upward growth
    while (start <= finish) {
/*
      fprintf (stdout, "do_markstack_stack: finish-start = %i\n", finish-start) ;
      fprintf (stdout, "do_markstack_stack: *start = %p\n", *start) ;
*/
      do_markstack_one(*start) ; ++start ;
     }
  } else { // downward growth
    while (start >= finish) {
/*
      fprintf (stdout, "do_markstack_stack: start-finish = %i\n", start-finish) ;
      fprintf (stdout, "do_markstack_stack: *start = %p\n", *start) ;
*/
      do_markstack_one(*start) ; --start ;
    }
  }
}

/* ****** ****** */

/* end of markstack.cats */

