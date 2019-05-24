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

void fprint_block1 (FILE* out, block1* p) {
  fprintf (out, "block1(%p): \n", p);
  fprintf (out, "  item_bsz = %i\n", p->item_bsz);
  fprintf (out, "  item_wsz = %i\n", p->item_wsz);
  fprintf (out, "  item_bin = %i\n", p->item_bin);
  fprintf (out, "  item_tot = %i\n", p->item_tot);
  fprintf (out, "  mark_cnt = %i\n", p->mark_cnt);
  fprintf (out, "  next = %p\n", p->next);
  fprintf (out, "  data = %p\n", p->data);
  fprintf (out, "  mark_bits = %p\n", p->mark_bits);
  fprintf (out, "  number_of_mark_bits = %i\n", (p->item_tot + 7) / 8);
}

block1* block1_malloc_word_bin(int iwsz, int ibin) {
  int itot, nmbs ; block1* p ;

  if (iwsz <= BLOCK_WORDSIZE) {
    itot = BLOCK_WORDSIZE / iwsz ;
  } else {
    itot = 1 ;
  }

  nmbs = (itot + 7) / 8 ; // number of bytes for mark bits
  p = (block1 *)malloc(sizeof(block1) + nmbs) ;
  if (!p) {
    ats_exit_errmsg(1, "Exit: [block1_malloc: malloc] failed.\n") ;
  }

  p->item_bsz = iwsz << NBYTE_PER_WORD_LOG ;
  p->item_wsz = iwsz ;
  p->item_bin = ibin ;
  p->item_tot = itot ;
  memset(p->mark_bits, 0, nmbs) ;

  if (iwsz <= BLOCK_WORDSIZE && the_freelst_blk) {
    p->data = (freeitm *)the_freelst_blk;
    the_freelst_blk = the_freelst_blk->next ;
    the_block1_count += 1;
    return p ;
  }

  if (itot > 1) {
    if (posix_memalign(&(p->data), BLOCK_BYTESIZE, BLOCK_BYTESIZE)) {
      ats_exit_errmsg(1, "Exit: [block1_malloc: memalign] failed.\n") ;
    }
    the_block1_count += 1;
  } else {
    if (posix_memalign(&(p->data), BLOCK_BYTESIZE, p->item_bsz)) {
      ats_exit_errmsg(1, "Exit: [block1_malloc: memalign] failed.\n") ;
    }
    the_block1_count += iwsz / BLOCK_WORDSIZE ;
  }

  return p ;
}

//

void block1_insert(block1* p) {
  freeitm p_data ;
  uintptr_t topseg, botseg ;
  botseg_table* tbl ;

  p_data = p->data ;
  topseg = PTR_TOPSEG_GET((uintptr_t)p_data) ;

  tbl = the_topseg_table[topseg] ;
  if (!tbl) {
    tbl = botseg_table_make() ; the_topseg_table[topseg] = tbl ;
  }
  botseg = PTR_BOTSEG_GET((uintptr_t)p_data) ;
  tbl->table[botseg] = p ;

  return ;
}

//

static inline
void block1_remove(freeitm p_data) {
  uintptr_t topseg, botseg ;
  botseg_table* tbl ;

  topseg = PTR_TOPSEG_GET((uintptr_t)p_data) ;

  tbl = the_topseg_table[topseg] ;
  botseg = PTR_BOTSEG_GET((uintptr_t)p_data) ;
  tbl->table[botseg] = (block1 *)0 ;

  return ;
}

void block1_free(block1* p) {
  freeitm p_data ;

/*
  fprintf (stdout, "block1_free: \n") ; fprint_block1 (stdout, p) ;
*/
  p_data = p->data ;

  // remove the block from the table tree
  block1_remove(p_data) ; 

  // return the block to the free list of blocks if it is not large
  // otherwise, free it.
  if (p->item_bsz <= BLOCK_BYTESIZE) {
    ((freelst)p_data)->next = the_freelst_blk ;
    the_freelst_blk = p_data ;
    the_block1_count -= 1 ;
  } else {
    free(p_data) ;
    the_block1_count -= (p->item_bsz >> BLOCK_BYTESIZE_LOG) ;
  }

  free(p) ;
  return ;
}

//

// [block1_freelst_link] links together all free items in a block
freelst block1_freelst_link(block1* p) {
  int i, ibsz, itot;
  uintptr_t offs ;
  freelst ans0, *ans ;
  byte* mbs; // mark bits

  ibsz = p->item_bsz ;
  itot = p->item_tot ;
  mbs = p->mark_bits ;
  offs = (uintptr_t)(p->data) ;
  ans = &ans0 ;

  i = 0 ; 
  while (i < itot) {
    if (IS_MARK_SET(mbs, i)) { i += 1; offs += ibsz ; continue ; }
    *ans = (freelst)offs ; ans = &(((freelst)offs)->next) ;
    i += 1; offs += ibsz;
  }
  *ans = (freelst)0 ;
/*
  fprintf(stderr, "--block1_freelst_link:\n") ; fprint_freelst(stderr, ans0) ;
*/
  return ans0 ;
}

/* ****** ****** */

/* end of blocklst1.cats */
