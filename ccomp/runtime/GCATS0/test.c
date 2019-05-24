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

/*

#include "ats_basics.h"
#include "ats_types.h"

#include "gc.cats"
#include "block0.cats"
#include "block1.cats"

*/

int main () {
  /*
  printf ("log2_floor(0) = %i\n", log2_floor(0)) ;
  printf ("log2_floor(15) = %i\n", log2_floor(15)) ;
  printf ("log2_floor(16) = %i\n", log2_floor(16)) ;

  printf ("log2_ceil(0) = %i\n", log2_ceil(0)) ;
  printf ("log2_ceil(15) = %i\n", log2_ceil(15)) ;
  printf ("log2_ceil(16) = %i\n", log2_ceil(16)) ;

  printf ("gc_stack_direction_get() = %i\n", gc_stack_direction_get()) ;
  printf ("div_ceil(31, 3) = %i\n", div_ceil (31, 3)) ;
  printf ("div_ceil(31, 4) = %i\n", div_ceil (31, 4)) ;
  printf ("mod_pow2(31, 1) = %i\n", mod_pow2 (31, 1)) ;
  printf ("mod_pow2(31, 4) = %i\n", mod_pow2 (31, 4)) ;

  the_stack_direction = stack_direction_get() ;
  the_stack_base = stack_base_get() ;
  printf ("the_stack_base = %p\n", the_stack_base) ;
  */

  printf ("ans = %i\n", 1 & 0+1) ;

}
