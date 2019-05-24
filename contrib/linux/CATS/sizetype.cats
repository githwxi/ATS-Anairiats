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

#ifndef ATSCTRB_LINUX_SIZETYPE_CATS
#define ATSCTRB_LINUX_SIZETYPE_CATS

/* ****** ****** */

#define atspre_int_of_size atspre_int1_of_size1
#define atspre_size_of_int1 atspre_size1_of_int1
#define atspre_uint_of_size atspre_uint1_of_size1
#define atspre_size_of_uint atspre_size1_of_uint1
#define atspre_int_of_ssize atspre_int1_of_ssize1
#define atspre_ssize_of_int atspre_ssize1_of_int1

#define atspre_add_size_int atspre_add_size1_int1
#define atspre_add_size_size atspre_add_size1_size1

#define atspre_sub_size_int atspre_sub_size1_int1
#define atspre_sub_size_size atspre_sub_size1_size1

#define atspre_mul_int_size atspre_mul_int1_size1
#define atspre_mul_size_int atspre_mul_size1_int1
#define atspre_mul_size_size atspre_mul_size1_size1

#define atspre_div_size_int atspre_div_size1_int1
#define atspre_div_size_size atspre_div_size1_size1

#define atspre_mod_size_int atspre_mod_size1_int1
#define atspre_mod_size_size atspre_mod_size1_size1

#define atspre_lt_size_size atspre_lt_size1_size1
#define atspre_lte_size_size atspre_lte_size1_size1

#define atspre_gt_size_int atspre_gt_size1_int1
#define atspre_gt_size_size atspre_gt_size1_size1
#define atspre_gte_size_int atspre_gte_size1_int1
#define atspre_gte_size_size atspre_gte_size1_size1

#define atspre_eq_size_int atspre_eq_size1_int1
#define atspre_eq_size_size atspre_eq_size1_size1

#define atspre_neq_size_int atspre_neq_size1_int1
#define atspre_neq_size_size atspre_neq_size1_size1

/* ****** ****** */

ATSinline()
ats_size_type
atspre_size_of_int
  (ats_int_type i) { return i ; }
// end of [atspre_size_of_int]

/* ****** ****** */

//
// unsigned size type
//

/* ****** ****** */

ATSinline()
ats_int_type
atspre_int1_of_size1
  (ats_size_type sz) { return sz ; }
// end of [atspre_int1_of_size1]

ATSinline()
ats_uint_type
atspre_uint1_of_size1
  (ats_size_type sz) { return sz ; }
// end of [atspre_uint1_of_size1]

/* ****** ****** */

ATSinline()
ats_size_type
atspre_size1_of_int1 (ats_int_type i) { return (ats_size_type)i ; }

ATSinline()
ats_size_type
atspre_size1_of_uint1 (ats_uint_type u) { return (ats_size_type)u ; }

ATSinline()
ats_size_type
atspre_size1_of_ptrdiff1 (ats_ptrdiff_type x) { return (ats_size_type)x ; }

/* ****** ****** */

ATSinline()
ats_size_type
atspre_lsl_size_int1 (ats_size_type sz, ats_int_type n) {
  return (sz << n) ;
}

ATSinline()
ats_size_type
atspre_lsr_size_int1 (ats_size_type sz, ats_int_type n) {
  return (sz >> n) ;
}

/* ****** ****** */

ATSinline()
ats_size_type
atspre_succ_size1 (ats_size_type sz) { return (sz + 1) ; }

ATSinline()
ats_size_type
atspre_pred_size1 (ats_size_type sz) { return (sz - 1) ; }

/* ****** ****** */

ATSinline()
ats_size_type
atspre_add_size1_int1 (ats_size_type sz1, ats_int_type i2) {
  return (sz1 + i2) ;
}

ATSinline()
ats_size_type
atspre_add_size1_size1 (
  ats_size_type sz1, ats_size_type sz2
) {
  return (sz1 + sz2) ;
} // end of [atspre_add_size1_size1]

/* ****** ****** */

ATSinline()
ats_size_type
atspre_sub_size1_int1 (ats_size_type sz1, ats_int_type i2) {
  return (sz1 - i2) ;
}

ATSinline()
ats_size_type
atspre_sub_size1_size1 (
  ats_size_type sz1, ats_size_type sz2
) {
  return (sz1 - sz2) ;
} // end of [atspre_sub_size1_size1]

/* ****** ****** */

ATSinline()
ats_size_type
atspre_mul_int1_size1 (ats_int_type i1, ats_size_type sz2) {
  return (i1 * sz2) ;
}

ATSinline()
ats_size_type
atspre_mul_size1_int1 (
  ats_size_type sz1, ats_int_type i2
) {
  return (sz1 * i2) ;
} // end of [atspre_mul_size1_int1]

ATSinline()
ats_size_type
atspre_mul_size1_size1 (
  ats_size_type sz1, ats_size_type sz2
) {
  return (sz1 * sz2) ;
} // end of [atspre_mul_size1_size1]

#define atspre_mul1_size1_size1 atspre_mul_size1_size1
#define atspre_mul2_size1_size1 atspre_mul_size1_size1

/* ****** ****** */

ATSinline()
ats_size_type
atspre_div_size1_int1 (
  ats_size_type sz1, ats_int_type i2
) {
  return (sz1 / i2) ;
} // end of [atspre_div_size1_int1]

#define atspre_div2_size1_int1 atspre_div_size1_int1

ATSinline()
ats_size_type
atspre_div_size1_size1 (
  ats_size_type sz1, ats_size_type sz2
) {
  return (sz1 / sz2) ;
} // end of [atspre_div_size1_size1]

#define atspre_div2_size1_size1 atspre_div_size1_size1

/* ****** ****** */

ATSinline()
ats_int_type
atspre_mod_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 % i2) ;
} // end of [atspre_mod_size1_int1]

#define atspre_mod1_size1_int1 atspre_mod_size1_int1
#define atspre_mod2_size1_int1 atspre_mod_size1_int1

ATSinline()
ats_size_type
atspre_mod_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 % sz2) ;
} // end of [atspre_mod_size1_size1]

#define atspre_mod1_size1_size1 atspre_mod_size1_size1
#define atspre_mod2_size1_size1 atspre_mod_size1_size1

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_lt_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 < sz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_lt_size1_size1]

ATSinline()
ats_bool_type
atspre_lt_int1_size1
  (ats_int_type i1, ats_size_type sz2) {
  return ((ats_size_type)i1 < sz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_lt_int1_size1]

ATSinline()
ats_bool_type
atspre_lt_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 < (ats_size_type)i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_lt_size1_int1]

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_lte_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 <= sz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_lte_size1_size1]

ATSinline()
ats_bool_type
atspre_lte_int1_size1
  (ats_int_type i1, ats_size_type sz2) {
  return ((ats_size_type)i1 <= sz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_lte_int1_size1]

ATSinline()
ats_bool_type
atspre_lte_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 <= (ats_size_type)i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_lte_size1_int1]

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_gt_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 > sz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_gt_size1_size1]

ATSinline()
ats_bool_type
atspre_gt_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 > (ats_size_type)i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_gt_size1_int1]

// ------ ------

ATSinline()
ats_bool_type
atspre_gte_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 >= sz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_gte_size1_size1]

ATSinline()
ats_bool_type
atspre_gte_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 >= (ats_size_type)i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_gte_size1_int1]

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_eq_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 == sz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_eq_size1_size1]

ATSinline()
ats_bool_type
atspre_eq_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 == (ats_size_type)i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_eq_size1_int1]

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_neq_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 != sz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_neq_size1_size1]

ATSinline()
ats_bool_type
atspre_neq_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 != (ats_size_type)i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_neq_size1_int1]

/* ****** ****** */

ATSinline()
ats_size_type
atspre_max_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 >= sz2 ? sz1 : sz2) ;
} // end of [atspre_max_size1_size1]

ATSinline()
ats_size_type
atspre_min_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 <= sz2 ? sz1 : sz2) ;
} // end of [atspre_min_size1_size1]

/* ****** ****** */
//
// signed size type (unindexed)
//
/* ****** ****** */

#define atspre_add_ssize_ssize atspre_add_ssize1_ssize1
#define atspre_sub_ssize_ssize atspre_sub_ssize1_ssize1
#define atspre_mul_ssize_ssize atspre_mul_ssize1_ssize1
#define atspre_div_ssize_ssize atspre_div_ssize1_ssize1

/* ****** ****** */

ATSinline()
ats_int_type
atspre_int1_of_ssize1
  (ats_ssize_type ssz) { return ssz ; }
// end of [atspre_int1_of_ssize1]

ATSinline()
ats_ssize_type
atspre_ssize1_of_int1
  (ats_int_type i) { return i ; }
// end of [atspre_ssize1_of_int1]

/* ****** ****** */

ATSinline()
ats_ssize_type
atspre_add_ssize1_ssize1 (
  ats_ssize_type i, ats_ssize_type j
) {
  return (i + j) ;
} // end of [atspre_add_ssize1_ssize1]

ATSinline()
ats_ssize_type
atspre_sub_ssize1_ssize1 (
  ats_ssize_type i, ats_ssize_type j
) {
  return (i - j) ;
} // end of [atspre_sub_ssize1_ssize1]

ATSinline()
ats_ssize_type
atspre_mul_ssize1_ssize1 (
  ats_ssize_type i, ats_ssize_type j
) {
  return (i * j) ;
} // end of [atspre_mul_ssize1_ssize1]

ATSinline()
ats_ssize_type
atspre_div_ssize1_ssize1 (
  ats_ssize_type i, ats_ssize_type j
) {
  return (i / j) ;
} // end of [atspre_div_ssize1_ssize1]

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_lt_ssize1_int1
  (ats_ssize_type ssz1, ats_int_type i2) {
  return (ssz1 < i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_lt_ssize1_int1]

// ------ ------

ATSinline()
ats_bool_type
atspre_lte_ssize1_int1
  (ats_ssize_type ssz1, ats_int_type i2) {
  return (ssz1 <= i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_lte_ssize1_int1]

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_gt_ssize1_int1
  (ats_ssize_type ssz1, ats_int_type i2) {
  return (ssz1 > i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_gt_ssize1_int1]

// ------ ------

ATSinline()
ats_bool_type
atspre_gte_ssize1_int1
  (ats_ssize_type ssz1, ats_int_type i2) {
  return (ssz1 >= i2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_gte_ssize1_int1]

/* ****** ****** */

ATSinline()
ats_bool_type
atspre_eq_ssize1_ssize1
  (ats_ssize_type ssz1, ats_ssize_type ssz2) {
  return (ssz1 == ssz2 ? ats_true_bool : ats_false_bool) ;
} // end of [atspre_eq_ssize1_ssize1]

ATSinline()
ats_bool_type
atspre_neq_ssize1_ssize1
  (ats_ssize_type ssz1, ats_ssize_type ssz2) {
  return (ssz1 != ssz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_eq_ssize1_ssize1] */

/* ****** ****** */

#endif /* ATSCTRB_LINUX_SIZETYPE_CATS */

/* end of [sizetype.cats] */
