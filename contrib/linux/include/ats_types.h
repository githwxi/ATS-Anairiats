/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Start Time: February, 2011
//
/* ****** ****** */

#ifndef ATS_TYPES_H
#define ATS_TYPES_H

/* ****** ****** */

typedef int ats_bool_type ;
typedef unsigned char ats_byte_type ;

typedef char ats_char_type ;
typedef signed char ats_schar_type ;
typedef unsigned char ats_uchar_type ;

typedef int ats_int_type ;
typedef unsigned int ats_uint_type ;

typedef long int ats_lint_type ;
typedef unsigned long int ats_ulint_type ;

typedef long long int ats_llint_type ;
typedef unsigned long long int ats_ullint_type ;

/*
typedef ssize_t ats_ssize_type ;
typedef ptrdiff_t ats_ptrdiff_type ;
typedef size_t ats_size_type ;
*/
typedef unsigned long int ats_size_type ;
typedef long int ats_ssize_type ;
typedef unsigned long int ats_ptrdiff_type ;

typedef void *ats_ptr_type ;
typedef void *ats_ref_type ;

typedef void ats_void_type ;

/* ****** ****** */

typedef void *ats_fun_ptr_type ;

typedef struct { void *closure_fun ; } ats_clo_type ;
typedef ats_clo_type *ats_clo_ptr_type ;
typedef ats_clo_type *ats_clo_ref_type ;

/* ****** ****** */

#endif /* ATS_TYPES_H */

/* end of [ats_types.h] */
