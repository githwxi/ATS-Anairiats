/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi.
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

#ifndef _LIBATS_THUNK_CATS
#define _LIBATS_THUNK_CATS

/* ****** ****** */

static inline
ats_ptr_type
atslib_thunk_make (ats_ptr_type x) {
  return x ;
}

static inline
ats_void_type
atslib_thunk_exec (ats_ptr_type f) {
  ((void (*)(ats_ptr_type))((ats_clo_ptr_type)f)->closure_fun)(f) ;
  ats_free_gc (f) ;
  return ;
}

/* ****** ****** */

static
ats_ptr_type
atslib_thunkopt_none = (ats_ptr_type)0 ;

static inline
ats_ptr_type
atslib_thunkopt_some (ats_ptr_type x) {
  return x ;
}

static inline
ats_bool_type
atslib_thunkopt_is_none (ats_ptr_type x) {
  return (x ? ats_false_bool : ats_true_bool) ;
}

static inline
ats_bool_type
atslib_thunkopt_is_some (ats_ptr_type x) {
  return (x ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_void_type
atslib_thunkopt_unnone (ats_ptr_type x) {
  return ;
}

static inline
ats_ptr_type
atslib_thunkopt_unsome (ats_ptr_type x) {
  return x ;
}

/* ****** ****** */

#endif /* _LIBATS_THUNK_CATS */

/* end of [thunk.cats] */
