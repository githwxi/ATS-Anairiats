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

// functions for sweeping

static inline
void markbits_clear_bot (botseg_table* tbl) {
  int i ; block1* p ;

  for (i = 0; i < BOTSEG_TABLE_SIZE; ++i) {
    p = tbl->table[i] ;
    if (p) {
/*
      fprintf(stderr, "--markbits_clear_bot:\n") ;
      fprint_block1(stderr, p) ;
*/
      p->mark_cnt = 0 ;
      memset (p->mark_bits, 0, (p->item_tot+7)/8) ;
    }
  }
  return ;
}

static inline
void markbits_clear_top () {
  int i ; botseg_table* tbl ;
  for (i = 0 ; i < TOPSEG_TABLE_SIZE ; ++i) {
    tbl = the_topseg_table[i] ;
    if (tbl) markbits_clear_bot (tbl) ;
  }
  return ;
}

#ifdef ATS_GC_FREEITM_UNMARK

// this is necessary only if there are many misidentified pointers

static inline
void freeitm_unmark (freeitm fi) {
  uintptr_t topseg, botseg, blkseg ;
  botseg_table* tbl ;
  block1* p ;

  topseg = PTR_TOPSEG_GET((uintptr_t)fi) ;
  tbl = the_topseg_table[topseg] ;

  if (!tbl) {
    atspre_exit_prerrf (1, "Exit: [freeitm_unmark(%p)] failed: invalid pointer\n", fi) ;
  }

  botseg = PTR_BOTSEG_GET((uintptr_t)fi) ;
  blkseg = PTR_BLKSEG_GET((uintptr_t)fi) ;

  fprintf(stderr, "--freeitm_unmark:\n") ;
  fprintf(stderr, "topseg = %i and botseg = %i and blkseg = %i\n", topseg, botseg, blkseg) ;

  p = tbl->table[botseg] ;

  if (!p) {
    atspre_exit_prerrf (1, "Exit: [freeitm_unmark(%p)] failed: invalid pointer\n", fi) ;
  }

  MARK_CLEAR(p->mark_bits, blkseg / p->item_wsz) ;

  return ;
}

#endif /* ATS_GC_FREEITM_UNMARK */

static inline
void freelst_arr_unmark () {
  int i ; freelst fai ;
  the_blocklst0_get() ;
  for (i = 0 ; i < NUMBER_OF_FREELSTS ; i++) {
#ifdef ATS_GC_FREEITM_UNMARK
    fai = the_freelst_arr[i] ;
    while (fai) {
      freeitm_unmark ((freeitm)fai) ; fai = fai->next ;
    }
#endif
    the_freelst_arr[i] = (freelst)0 ;
  }
  the_blocklst0_set() ;
  return ;
}

//

double the_block_sweep_cutoff = 0.01 * BLOCK_SWEEP_CUTOFF_PERCENT ;

static inline
void sweeplst_build_bot (botseg_table* tbl) {
  int i, mark_cnt ; block1* p ;
  i = 0 ;
  while (i < BOTSEG_TABLE_SIZE) {
    p = tbl->table[i] ; ++i ;
    if (!p) continue ;
    mark_cnt = p->mark_cnt ;
    if (!mark_cnt) { block1_free(p) ; continue ; }
    if (mark_cnt > p->item_tot * the_block_sweep_cutoff) continue ;
    p->next = the_sweeplst_arr[p->item_bin] ;
    the_sweeplst_arr[p->item_bin] = p ;
  }
  return ;
}

static inline
void sweeplst_build_top () {
  int i ; botseg_table* tbl ;
  for (i = 0 ; i < NUMBER_OF_FREELSTS ; ++i) {
    the_sweeplst_arr[i] = (blocklst1)0 ;
  }
  for (i = 0 ; i < TOPSEG_TABLE_SIZE ; ++i) {
    tbl = the_topseg_table[i] ;
    if (tbl) sweeplst_build_bot (tbl) ;
  }
}

/* ****** ****** */

/* end of sweeping.cats */

