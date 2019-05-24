// /***********************************************************************/
// /*                                                                     */
// /*                         Applied Type System                         */
// /*                                                                     */
// /*                              Hongwei Xi                             */
// /*                                                                     */
// /***********************************************************************/

// /*
//  * ATS - Unleashing the Power of Types!
// *
// * Copyright (C) 2002-2007 Hongwei Xi, Boston University
// *
// * All rights reserved
// *
// * ATS is free software;  you can  redistribute it and/or modify it under
// * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
// * Free Software Foundation; either version 2.1, or (at your option)  any
// * later version.
// * 
// * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
// * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
// * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
// * for more details.
// * 
// * You  should  have  received  a  copy of the GNU General Public License
// * along  with  ATS;  see the  file COPYING.  If not, please write to the
// * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
// * 02110-1301, USA.
// *
// */

// /* ****** ****** */

// /* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

// /* ****** ****** */

// Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu )

// This file may need to be generated according to some system parameters

#define __WORDSIZE 32
#define NBYTE_PER_WORD_LOG 2

//

#define NBIT_PER_BYTE 8
#define NBYTE_PER_WORD (1 << NBYTE_PER_WORD_LOG)

//

#define PTR_BLKSEG_SIZE 11
#define PTR_BOTSEG_SIZE 10
#define PTR_BOTBLKSEG_SIZE (PTR_BLKSEG_SIZE + PTR_BOTSEG_SIZE)
#define PTR_TOPSEG_SIZE (__WORDSIZE - NBYTE_PER_WORD_LOG - PTR_BOTBLKSEG_SIZE)

//

#define BLOCK_WORDSIZE_LOG PTR_BLKSEG_SIZE
#define BLOCK_WORDSIZE (1 << BLOCK_WORDSIZE_LOG)
#define BLOCK_BYTESIZE_LOG (BLOCK_WORDSIZE_LOG + NBYTE_PER_WORD_LOG)
#define BLOCK_BYTESIZE (BLOCK_WORDSIZE << NBYTE_PER_WORD_LOG)

//

#define FREEITM_SIZE_CUTOFF_LOG 4
#define FREEITM_SIZE_CUTOFF (1 << FREEITM_SIZE_CUTOFF_LOG)
#define NUMBER_OF_FREELSTS (FREEITM_SIZE_CUTOFF-FREEITM_SIZE_CUTOFF_LOG+PTR_BLKSEG_SIZE)

//

#define MAX_MARKSTACK_POSITION 4095
#define MARKSTACK_CUTOFF (BLOCK_WORDSIZE / 2)
#define BLOCK_SWEEP_CUTOFF_PERCENT 80
#define BLOCK_LIMIT_EXTEND_CUTOFF_PERCENT 75

//

#define GLOBALS_ENTRY_PAGESIZE 128

// /* ****** *******/

// /* end of [gc.hats] */
