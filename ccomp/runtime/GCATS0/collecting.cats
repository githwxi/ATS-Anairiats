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

double the_block_limit_extend_cutoff =
  BLOCK_LIMIT_EXTEND_CUTOFF_PERCENT * 0.01 ;

void do_collection() {
  jmp_buf reg_save ;
  
  setjmp(reg_save) ; // register contents need to be scanned
  asm volatile ("": : :"memory") ; // prevent agressive optimization
/*
  fprintf(
    stderr,
    "GC begins: the_block1_count = %i and the_block1_limit = %i\n",
    the_block1_count, the_block1_limit
  ) ;
*/
  markstack_init() ;
  markbits_clear_top() ;
  do_markstack_globals() ;
  do_markstack_blocklst0() ;
  do_markstack_stack() ;
  freelst_arr_unmark() ;
  sweeplst_build_top() ;
/*
  fprintf(
    stderr,
    "GC ends: the_block1_count = %i and the_block1_limit = %i\n",
    the_block1_count, the_block1_limit
  ) ;
*/
  if (the_block1_limit >= the_block1_limit_max) return ;

  if (the_block1_count >= the_block1_limit * the_block_limit_extend_cutoff)
    the_block1_limit *= 2 ;

  return ;
}
