/* ******************************************************************* */
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/* ******************************************************************* */

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

/*
**
** [gcats2_master.hats]: the header file for GCATS2; it is used to generate
** [gcats2_ats.hats] and [gcats2_c.hats]; the former is used in ATS and the
** latter is used in [gcats2_c.hats].
**
*/

/* ****** ****** */

#if _ATSHEADER
#define __ATS(x) x
#else
#define __ATS(x) // dropping lines that are ATS-specific
#endif

#if _CHEADER
#define __C(x) x
#else
#define __C(x)   // dropping lines that are C-specific
#endif

/* ****** ****** */

#define __define #define
#define __else #else
#define __endif #endif
#define __error #error
#define __if #if
#define __ifdef #ifdef
#define __ifndef #ifndef
#define __include #include

/* ****** ****** */

__include "config.h" // automatically generated in $(ATSHOME)

/* ****** ****** */

__C(#ifndef GCATS2_C_H)
__C(#define GCATS2_C_H)

__ATS(#ifndef GCATS2_ATS_HATS)
__ATS(#define GCATS2_ATS_HATS)

/* ****** ****** */

__define NBIT_PER_BYTE 8
__define NBIT_PER_BYTE_LOG 3
__ATS(#assert (NBIT_PER_BYTE == 1 << NBIT_PER_BYTE_LOG))
__define NBIT_PER_BYTE_MASK (NBIT_PER_BYTE - 1)

/* ****** ****** */

__ATS(#if (SIZEOF_VOIDP * NBIT_PER_BYTE == 32))
__ATS(#define __WORDSIZE 32)
__ATS(#endif)

__ATS(#if (SIZEOF_VOIDP * NBIT_PER_BYTE == 64))
__ATS(#define __WORDSIZE 64)
__ATS(#endif)

__ATS(#print "__WORDSIZE = "; #print __WORDSIZE; #print "\n")

__if (__WORDSIZE != 32) // #then
__if (__WORDSIZE != 64) // #then
__error "__WORDSIZE is neither 32 nor 64!\n"
__endif
__endif

/* ****** ****** */

__define __PAGESIZE 4096

/* ****** ****** */

__C(#undef NBIT_PER_WORD)
__C(#undef NBIT_PER_WORD_LOG)

__define NBIT_PER_WORD __WORDSIZE

__if (__WORDSIZE == 32) // #then
__define NBIT_PER_WORD_LOG 5
__define NBYTE_PER_WORD 4
__define NBYTE_PER_WORD_LOG 2
__endif // end of [__WORDSIZE == 32]

__if (__WORDSIZE == 64) // #then
__define NBIT_PER_WORD_LOG 6
__define NBYTE_PER_WORD 8
__define NBYTE_PER_WORD_LOG 3
__endif // end of [__WORDSIZE == 64]

__ATS(#assert (NBIT_PER_WORD == 1 << NBIT_PER_WORD_LOG))
__ATS(#assert (NBIT_PER_WORD == NBIT_PER_BYTE * NBYTE_PER_WORD))
__ATS(#assert (NBYTE_PER_WORD == 1 << NBYTE_PER_WORD_LOG))

__define NBYTE_PER_WORD_MASK (NBYTE_PER_WORD - 1)

/* ****** ****** */

__define GCATS2_TEST 1 // a flag for testing
__define GCATS2_DEBUG 1 // a flag for debugging

/* ****** ****** */

/*
**
** A pointer is of the following form:
**
** -----------------------------------
** | TOPSEG | BOTSEG | CHKSEG | 0..0 |
** -----------------------------------
**
*/

__if (__WORDSIZE == 32)
__define PTR_CHKSEG_SIZE 10
__endif

__if (__WORDSIZE == 64)
__define PTR_CHKSEG_SIZE 9
__endif

__ATS(#print "PTR_CHKSEG_SIZE = "; #print PTR_CHKSEG_SIZE; #print "\n")

/* ****** ****** */

__define PTR_BOTSEG_SIZE 10
__ATS(#print "PTR_BOTSEG_SIZE = "; #print PTR_BOTSEG_SIZE; #print "\n")
__define PTR_BOTCHKSEG_SIZE (PTR_BOTSEG_SIZE + PTR_CHKSEG_SIZE)
__define PTR_TOPSEG_SIZE (NBIT_PER_WORD - PTR_BOTCHKSEG_SIZE - NBYTE_PER_WORD_LOG)
__ATS(#print "PTR_TOPSEG_SIZE = "; #print PTR_TOPSEG_SIZE; #print "\n")

/* ****** ****** */

__C(#define CHKSEG_TABLESIZE (1 << PTR_CHKSEG_SIZE))
__ATS(#define CHKSEG_TABLESIZE %(1 << PTR_CHKSEG_SIZE))
__ATS(#print "CHKSEG_TABLESIZE = "; #print CHKSEG_TABLESIZE; #print "\n")
__define CHKSEG_TABLESIZE_MASK (CHKSEG_TABLESIZE - 1)

__C(#define BOTSEG_TABLESIZE (1 << PTR_BOTSEG_SIZE))
__ATS(#define BOTSEG_TABLESIZE %(1 << PTR_BOTSEG_SIZE))
__ATS(#print "BOTSEG_TABLESIZE = "; #print BOTSEG_TABLESIZE; #print "\n")
__define BOTSEG_TABLESIZE_MASK (BOTSEG_TABLESIZE - 1)

__if (__WORDSIZE == 32)
__define TOPSEG_TABLESIZE (1 << PTR_TOPSEG_SIZE)
__endif

__if (__WORDSIZE == 64)
__define TOPSEG_HASHTABLESIZE 4096
__define TOPSEG_HASHTABLESIZE_LOG 12
__define TOPSEG_HASHTABLESIZE_MASK (TOPSEG_HASHTABLESIZE - 1)
__ATS(#assert (TOPSEG_HASHTABLESIZE == 1 << TOPSEG_HASHTABLESIZE_LOG))
__endif

/* ****** ****** */

__define CHUNK_WORDSIZE_LOG PTR_CHKSEG_SIZE
__C(#define CHUNK_WORDSIZE (1 << CHUNK_WORDSIZE_LOG))
__ATS(#define CHUNK_WORDSIZE %(1 << CHUNK_WORDSIZE_LOG))
__define CHUNK_WORDSIZE_MASK (CHUNK_WORDSIZE - 1)
__ATS(#print "CHUNK_WORDSIZE = "; #print CHUNK_WORDSIZE; #print "\n")

__define CHUNK_BYTESIZE_LOG (CHUNK_WORDSIZE_LOG + NBYTE_PER_WORD_LOG)
__define CHUNK_BYTESIZE (1 << CHUNK_BYTESIZE_LOG)
__define CHUNK_BYTESIZE_MASK (CHUNK_BYTESIZE - 1)
__ATS(#print "CHUNK_BYTESIZE = "; #print CHUNK_BYTESIZE; #print "\n")
__ATS(#assert (CHUNK_BYTESIZE == __PAGESIZE))

/* ****** ****** */

__define MAX_CLICK_WORDSIZE_LOG CHUNK_WORDSIZE_LOG
__C(#define MAX_CLICK_WORDSIZE (1 << MAX_CLICK_WORDSIZE_LOG))
__ATS(#define MAX_CLICK_WORDSIZE %(1 << MAX_CLICK_WORDSIZE_LOG))
__ATS(#assert (MAX_CLICK_WORDSIZE <= CHUNK_WORDSIZE))
__ATS(#print "MAX_CLICK_WORDSIZE = "; #print MAX_CLICK_WORDSIZE; #print "\n")

/* ****** ****** */

/*
** the_freeitmlst_array:
**   [ 2^0 | 2^1 | ... | 2^MAX_CLICK_WORDSIZE_LOG]
*/
__define FREEITMLST_ARRAYSIZE (MAX_CLICK_WORDSIZE_LOG + 1)

/* ****** ****** */

__define MARKSTACK_PAGESIZE 4000
/*
** MARKSTACK/TOTWSZ =(approximately) 1/NCHUNK_PER_MARKSTACKPAGE
*/
__define NCHUNK_PER_MARKSTACKPAGE 64
__define NMARKSTACKPAGE_OVERFLOW_EXTEND 2

__define MARKSTACK_CUTOFF (CHUNK_WORDSIZE / 4)
__define CHUNK_SWEEP_CUTOFF 0.50 // 50%
__ATS(#assert (0.0 <= CHUNK_SWEEP_CUTOFF))
__ATS(#assert (CHUNK_SWEEP_CUTOFF <= 1.0))
__define TOTWSZ_LIMIT_EXTEND_CUTOFF 0.75 // 75%
__ATS(#assert (0.0 <= TOTWSZ_LIMIT_EXTEND_CUTOFF))
__ATS(#assert (TOTWSZ_LIMIT_EXTEND_CUTOFF <= 1.0))

/* ****** ****** */

__define GLOBALRTS_PAGESIZE 100 // more or less chosen arbitrarily
__ATS(#assert (GLOBALRTS_PAGESIZE >= 1))

/* ****** ****** */

#ifndef _ATS_MULTITHREAD
__define _ATS_MULTITHREAD 0
#else
#undef _ATS_MULTITHREAD
__define _ATS_MULTITHREAD 1
#endif // end of [_ATS_MULTITHREAD]

/* ****** ****** */

__C(#endif) // end of [#ifndef GCATS2_C_H]
__ATS(#endif) // end of [#ifndef GCATS2_ATS_HATS]

/* ****** ****** */

/* end of [gcats2_master.hats] */
