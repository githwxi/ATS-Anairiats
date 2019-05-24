/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATS_LIBC_FLOAT_CATS
#define ATS_LIBC_FLOAT_CATS

/* ****** ****** */

#include <float.h>

/* ****** ****** */

#ifndef DBL_RADIX
#define DBL_RADIX FLT_RADIX
#endif
#ifndef LDBL_RADIX
#define LDBL_RADIX FLT_RADIX
#endif

/* ****** ****** */

#ifndef DBL_ROUNDS
#define DBL_ROUNDS FLT_ROUNDS
#endif
#ifndef LDBL_ROUNDS
#define LDBL_ROUNDS FLT_ROUNDS
#endif

/* ****** ****** */

#endif /* ATS_LIBC_FLOAT_CATS */

/* end of [float.cats] */
