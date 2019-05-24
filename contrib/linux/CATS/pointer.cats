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
** Copyright (C) 2002-2011 Hongwei Xi.
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

#ifndef ATSCTRB_LINUX_POINTER_CATS
#define ATSCTRB_LINUX_POINTER_CATS

/* ****** ****** */

static
ats_ptr_type atspre_null_ptr = (ats_ptr_type)0 ;

ATSinline()
ats_bool_type
atspre_ptr_is_null
  (ats_ptr_type p) {
  return (p == (ats_ptr_type)0 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_ptr_is_null]

ATSinline()
ats_bool_type
atspre_ptr_isnot_null
  (ats_ptr_type p) {
  return (p != (ats_ptr_type)0 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_ptr_isnot_null]

/* ****** ****** */

ATSinline()
ats_void_type
atspre_ptr_free_null (ats_ptr_type p) { return ; }

/* ****** ****** */

ATSinline()
ats_ptr_type
atspre_psucc (ats_ptr_type p) {
  return (ats_ptr_type)((ats_byte_type*)p + 1) ;
} // end of [atspre_psucc]

ATSinline()
ats_ptr_type
atspre_ppred (ats_ptr_type p) {
  return (ats_ptr_type)((ats_byte_type*)p - 1) ;
} // end of [atspre_ppred]

/* ****** ****** */

ATSinline()
ats_ptr_type
atspre_padd_int (
  ats_ptr_type p, ats_int_type n
) {
  return (ats_ptr_type)((ats_byte_type*)p + n) ;
} // end of [atspre_padd_int]

ATSinline()
ats_ptr_type
atspre_padd_size (
  ats_ptr_type p, ats_size_type n
) {
  return (ats_ptr_type)((ats_byte_type*)p + n) ;
} // end of [atspre_padd_size]

ATSinline()
ats_ptr_type
atspre_psub_int (
  ats_ptr_type p, ats_int_type n
) {
  return (ats_ptr_type)((ats_byte_type*)p - n) ;
} // end of [atspre_psub_int]

ATSinline()
ats_ptr_type
atspre_psub_size (
  ats_ptr_type p, ats_size_type n
) {
  return (ats_ptr_type)((ats_byte_type*)p - n) ;
} // end of [atspre_psub_size]

ATSinline()
ats_ptrdiff_type
atspre_pdiff (
  ats_ptr_type p1, ats_ptr_type p2
) {
  return ((ats_byte_type*)p1 - (ats_byte_type*)p2) ;
}

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_plt (ats_ptr_type p1, ats_ptr_type p2) {
  return (p1 < p2) ;
}

ATSinline()
ats_bool_type
atspre_plte (ats_ptr_type p1, ats_ptr_type p2) {
  return (p1 <= p2) ;
}

ATSinline()
ats_bool_type
atspre_pgt (ats_ptr_type p1, ats_ptr_type p2) {
  return (p1 > p2) ;
}

ATSinline()
ats_bool_type
atspre_pgte (ats_ptr_type p1, ats_ptr_type p2) {
  return (p1 >= p2) ;
}

ATSinline()
ats_bool_type
atspre_peq (ats_ptr_type p1, ats_ptr_type p2) {
  return (p1 == p2) ;
}

ATSinline()
ats_bool_type
atspre_pneq (ats_ptr_type p1, ats_ptr_type p2) {
  return (p1 != p2) ;
}

ATSinline()
ats_int_type
atspre_compare_ptr_ptr (
  ats_ptr_type p1, ats_ptr_type p2
) {
  if (p1 < p2) return (-1) ;
  else if (p1 > p2) return ( 1) ;
  else return (0) ;  
} /* end of [atspre_compare_ptr_ptr] */

/* ****** ****** */

#endif /* ATSCTRB_LINUX_POINTER_CATS */

/* end of [pointer.cats] */
