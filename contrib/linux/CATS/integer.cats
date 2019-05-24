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

#ifndef ATSCTRB_LINUX_INTEGER_CATS
#define ATSCTRB_LINUX_INTEGER_CATS

/* ****** ****** */
//
// signed integers
//
/* ****** ****** */

ATSinline()
ats_int_type
atspre_int_of_char (ats_char_type c) { return c ; }

ATSinline()
ats_int_type
atspre_int_of_schar (ats_schar_type c) { return c ; }

ATSinline()
ats_int_type
atspre_int_of_uchar (ats_uchar_type c) { return c ; }

ATSinline()
ats_int_type
atspre_abs_int
  (ats_int_type i) { return (i >= 0 ? i : -i) ; }
// end of [atspre_abs_int]

ATSinline()
ats_int_type
atspre_neg_int (ats_int_type i) { return (-i) ; }

ATSinline()
ats_int_type
atspre_succ_int (ats_int_type i) { return (i + 1) ; }

ATSinline()
ats_int_type
atspre_pred_int (ats_int_type i) { return (i - 1) ; }

ATSinline()
ats_int_type
atspre_add_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 + i2) ;
}

ATSinline()
ats_int_type
atspre_sub_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 - i2) ;
}

ATSinline()
ats_int_type
atspre_mul_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 * i2) ;
}

ATSinline()
ats_int_type
atspre_div_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 / i2) ;
}

ATSinline()
ats_int_type
atspre_mod_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 % i2) ;
}

ATSinline()
ats_bool_type
atspre_lt_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 < i2) ;
}

ATSinline()
ats_bool_type
atspre_lte_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 <= i2) ;
}

ATSinline()
ats_bool_type
atspre_gt_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 > i2) ;
}

ATSinline()
ats_bool_type
atspre_gte_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 >= i2) ;
}

ATSinline()
ats_bool_type
atspre_eq_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 == i2) ;
}

ATSinline()
ats_bool_type
atspre_neq_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 != i2) ;
}

//
// compare, max and min
//

ATSinline()
ats_int_type
atspre_compare_int_int (
  ats_int_type i1, ats_int_type i2
) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
} // end of [atspre_compare_int_int]

ATSinline()
ats_int_type
atspre_max_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 >= i2) ? i1 : i2 ;
}

ATSinline()
ats_int_type
atspre_min_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 <= i2) ? i1 : i2 ;
}

//
// square, cube and pow functions
//

ATSinline()
ats_int_type
atspre_square_int (ats_int_type i) { return (i * i) ; }

ATSinline()
ats_int_type
atspre_cube_int (ats_int_type i) { return (i * i * i) ; }

ATSinline()
ats_int_type
atspre_pow_int_int1 (
  ats_int_type x, ats_int_type n
) {
  int res = 1;
//
  while (n > 0) {
    if (n % 2 > 0) { res *= x ; x = x * x ; }
    else { x = x * x ; }
    n = n >> 1 ;
  } // end of [while]
//
  return res ;
} // end of [atspre_pow_int_int1]

//
// greatest common division
//

ATSinline()
ats_int_type
atspre_gcd_int_int (
  ats_int_type m0, ats_int_type n0
) {
  int m, n, t ;
//
  if (m0 >= 0) m = m0; else m = -m0 ;
  if (n0 >= 0) n = n0; else n = -n0 ;
//
  while (m) { t = n % m ; n = m ; m = t ; }
//
  return n ;
//
} // end of [atspre_gcd_int_int]

//
// bitwise operations
//

ATSinline()
ats_int_type
atspre_asl_int_int1 (ats_int_type i, ats_int_type n) {
  return i << n ;
}

ATSinline()
ats_int_type
atspre_asr_int_int1 (ats_int_type i, ats_int_type n) {
  return i >> n ;
}

/* ****** ****** */
//
// unsigned integers
//
/* ****** ****** */

ATSinline()
ats_uint_type
atspre_uint_of_char
  (ats_char_type c) { return ((unsigned char)c) ; }
// end of [atspre_uint_of_char]

ATSinline()
ats_uint_type
atspre_uint_of_uchar
  (ats_uchar_type c) { return ((unsigned char)c) ; }
// end of [atspre_uint_of_uchar]

ATSinline()
ats_uint_type
atspre_succ_uint (ats_uint_type i) { return (i + 1) ; }

ATSinline()
ats_uint_type
atspre_pred_uint (ats_uint_type i) { return (i - 1) ; }

ATSinline()
ats_uint_type
atspre_add_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 + i2) ;
} // end of [atspre_add_uint_uint]

ATSinline()
ats_uint_type
atspre_sub_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 - i2) ;
} // end of [atspre_sub_uint_uint]

ATSinline()
ats_uint_type
atspre_mul_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 * i2) ;
} // end of [atspre_mul_uint_uint]

ATSinline()
ats_uint_type
atspre_div_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 / i2) ;
} // end of [atspre_div_uint_uint]

ATSinline()
ats_uint_type
atspre_mod_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 % i2) ;
} // end of [atspre_mod_uint_uint]

ATSinline()
ats_bool_type
atspre_lt_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 < i2) ;
} // end of [atspre_lt_uint_uint]

ATSinline()
ats_bool_type
atspre_lte_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 <= i2) ;
} // end of [atspre_lte_uint_uint]

ATSinline()
ats_bool_type
atspre_gt_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 > i2) ;
} // end of [atspre_gt_uint_uint]

ATSinline()
ats_bool_type
atspre_gte_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 >= i2) ;
} // end of [atspre_gte_uint_uint]

ATSinline()
ats_bool_type
atspre_eq_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 == i2) ;
} // end of [atspre_eq_uint_uint]

ATSinline()
ats_bool_type
atspre_neq_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 != i2) ;
} // end of [atspre_neq_uint_uint]

//
// compare, max and min
//

ATSinline()
ats_int_type
atspre_compare_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
} // end of [atspre_compare_uint_uint]

ATSinline()
ats_uint_type
atspre_max_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 >= i2 ? i1 : i2) ;
} // end of [atspre_max_uint_uint]

ATSinline()
ats_uint_type
atspre_min_uint_uint (
  ats_uint_type i1, ats_uint_type i2
) {
  return (i1 <= i2 ? i1 : i2) ;
} // end of [atspre_min_uint_uint]

//
// square and cube
//

ATSinline()
ats_uint_type
atspre_square_uint (ats_uint_type u) { return (u * u) ; }

ATSinline()
ats_uint_type
atspre_cube_uint (ats_uint_type u) { return (u * u * u) ; }

/*
** bitwise operations
*/

ATSinline()
ats_uint_type
atspre_lnot_uint (ats_uint_type x) { return (~x) ; }

ATSinline()
ats_uint_type
atspre_land_uint_uint (ats_uint_type x, ats_uint_type y) {
  return (x & y) ;
}

ATSinline()
ats_uint_type
atspre_lor_uint_uint (ats_uint_type x, ats_uint_type y) {
  return (x | y) ;
}

ATSinline()
ats_uint_type
atspre_lxor_uint_uint (ats_uint_type x, ats_uint_type y) {
  return (x ^ y) ;
}

/*
** logical shifting operations
*/

ATSinline()
ats_uint_type
atspre_lsl_uint_int1 (
  ats_uint_type u, ats_int_type n
) {
  return (u << n) ;
} // end of [atspre_lsl_uint_int1]

ATSinline()
ats_uint_type
atspre_lsr_uint_int1 (
  ats_uint_type u, ats_int_type n
) {
  return (u >> n) ;
} // end of [atspre_lsr_uint_int1]

#define atspre_lsl_uint_uint atspre_lsl_uint_int1
#define atspre_lsr_uint_uint atspre_lsr_uint_int1

/* ****** ****** */

#define atspre_iabs atspre_abs_int
#define atspre_ineg atspre_neg_int

#define atspre_isucc atspre_succ_int
#define atspre_ipred atspre_pred_int

#define atspre_iadd atspre_add_int_int
#define atspre_isub atspre_sub_int_int
#define atspre_imul atspre_mul_int_int
#define atspre_imul1 atspre_mul_int_int
#define atspre_imul2 atspre_mul_int_int
#define atspre_idiv atspre_div_int_int
#define atspre_idiv1 atspre_div_int_int

#define atspre_nmul atspre_mul_int_int
#define atspre_ndiv atspre_div_int_int
#define atspre_ndiv2 atspre_div_int_int

#define atspre_nmod atspre_mod_int_int
#define atspre_nmod1 atspre_mod_int_int

#define atspre_ilt atspre_lt_int_int
#define atspre_ilte atspre_lte_int_int
#define atspre_igt atspre_gt_int_int
#define atspre_igte atspre_gte_int_int
#define atspre_ieq atspre_eq_int_int
#define atspre_ineq atspre_neq_int_int

#define atspre_icompare atspre_compare_int_int
#define atspre_imax atspre_max_int_int
#define atspre_imin atspre_min_int_int

#define atspre_ipow atspre_pow_int_int1
#define atspre_npow atspre_pow_int_int1

ATSinline()
ats_int_type
atspre_ihalf (ats_int_type n) { return (n / 2) ; }

ATSinline()
ats_int_type
atspre_nhalf (ats_int_type n) { return (n >> 1) ; }

/* ****** ****** */

#define atspre_uadd atspre_add_uint_uint
#define atspre_usub atspre_sub_uint_uint
#define atspre_umul atspre_mul_uint_uint
#define atspre_udiv atspre_div_uint_uint
#define atspre_umod atspre_mod_uint_uint

//

ATSinline()
ats_int_type
atspre_uimod (
  ats_uint_type u1, ats_int_type i2
) {
  return (u1 % ((ats_uint_type)i2)) ;
} /* end of [atspre_uimod] */

#define atspre_ult atspre_lt_uint_uint
#define atspre_ulte atspre_lte_uint_uint
#define atspre_ugt atspre_gt_uint_uint
#define atspre_ugte atspre_gte_uint_uint
#define atspre_ueq atspre_eq_uint_uint
#define atspre_uneq atspre_neq_uint_uint

#define atspre_ucompare atspre_compare_uint_uint
#define atspre_umax atspre_max_uint_uint
#define atspre_umin atspre_min_uint_uint

/* ****** ****** */
//
// signed long integers
//
/* ****** ****** */

ATSinline()
ats_lint_type
atspre_lint_of_int (ats_int_type i) { return i ; }

ATSinline()
ats_int_type
atspre_int_of_lint (ats_lint_type li) { return li ; }

//
// HX: arithmetic functions and comparison functions
//

ATSinline()
ats_lint_type
atspre_abs_lint (ats_lint_type i) {
  return (i >= 0 ? i : -i) ;
}

ATSinline()
ats_lint_type
atspre_neg_lint (ats_lint_type i) {
  return (-i) ;
}

ATSinline()
ats_lint_type
atspre_succ_lint (ats_lint_type i) { return (i + 1) ; }

ATSinline()
ats_lint_type
atspre_pred_lint (ats_lint_type i) { return (i - 1) ; }

ATSinline()
ats_lint_type
atspre_add_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 + i2) ;
}

ATSinline()
ats_lint_type
atspre_sub_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 - i2) ;
}

ATSinline()
ats_lint_type
atspre_mul_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 * i2) ;
}

ATSinline()
ats_lint_type
atspre_div_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 / i2) ;
}

ATSinline()
ats_lint_type
atspre_mod_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 % i2) ;
}

ATSinline()
ats_bool_type
atspre_lt_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 < i2) ;
}

ATSinline()
ats_bool_type
atspre_lte_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 <= i2) ;
}

ATSinline()
ats_bool_type
atspre_gt_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 > i2) ;
}

ATSinline()
ats_bool_type
atspre_gte_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 >= i2) ;
}

ATSinline()
ats_bool_type
atspre_eq_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 == i2) ;
}

ATSinline()
ats_bool_type
atspre_neq_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 != i2) ;
}

// compare, max and min

ATSinline()
ats_int_type
atspre_compare_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  if (i1 < i2) return (-1) ;
  else if (i1 > i2) return ( 1) ;
  else return (0) ;
}

ATSinline()
ats_lint_type
atspre_max_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 >= i2 ? i1 : i2) ;
}

ATSinline()
ats_lint_type
atspre_min_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 <= i2 ? i1 : i2) ;
}

/* unsigned long integers */

/* ****** ****** */

ATSinline()
ats_ulint_type
atspre_ulint_of_int (ats_int_type i) { return i ; }

ATSinline()
ats_int_type
atspre_int_of_ulint (ats_ulint_type ul) { return ul ; }

//

ATSinline()
ats_ulint_type
atspre_ulint_of_uint (ats_uint_type u) { return u ; }

ATSinline()
ats_uint_type
atspre_uint_of_ulint (ats_ulint_type ul) { return ul ; }

/* ****** ****** */

ATSinline()
ats_ulint_type
atspre_succ_ulint (ats_ulint_type i) { return (i + 1) ; }

ATSinline()
ats_ulint_type
atspre_pred_ulint (ats_ulint_type i) { return (i - 1) ; }

ATSinline()
ats_ulint_type
atspre_add_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 + i2) ;
}

ATSinline()
ats_ulint_type
atspre_sub_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 - i2) ;
}

ATSinline()
ats_ulint_type
atspre_mul_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 * i2) ;
}

ATSinline()
ats_ulint_type
atspre_div_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 / i2) ;
}

ATSinline()
ats_ulint_type
atspre_mod_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 % i2) ;
}

ATSinline()
ats_bool_type
atspre_lt_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 < i2) ;
}

ATSinline()
ats_bool_type
atspre_lte_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 <= i2) ;
}

ATSinline()
ats_bool_type
atspre_gt_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 > i2) ;
}

ATSinline()
ats_bool_type
atspre_gte_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 >= i2) ;
}

ATSinline()
ats_bool_type
atspre_eq_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 == i2) ;
}

ATSinline()
ats_bool_type
atspre_neq_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 != i2) ;
}

//
// compare, max and min
//

ATSinline()
ats_int_type
atspre_compare_ulint_ulint (
  ats_ulint_type i1, ats_ulint_type i2
) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
} // end of [atspre_compare_ulint_ulint]

ATSinline()
ats_ulint_type
atspre_max_ulint_ulint (
  ats_ulint_type i1
, ats_ulint_type i2
) {
  return (i1 >= i2 ? i1 : i2) ;
} // end of [atspre_max_ulint_ulint]

ATSinline()
ats_ulint_type
atspre_min_ulint_ulint (
  ats_ulint_type i1
, ats_ulint_type i2
) {
  return (i1 <= i2 ? i1 : i2) ;
} // end of [atspre_min_ulint_ulint]

//
// bitwise operations
//

ATSinline()
ats_ulint_type
atspre_lnot_ulint (ats_ulint_type x) { return (~x) ; }

ATSinline()
ats_ulint_type
atspre_land_ulint_ulint (ats_ulint_type x, ats_ulint_type y) {
  return (x & y) ;
}

ATSinline()
ats_ulint_type
atspre_lor_ulint_ulint (ats_ulint_type x, ats_ulint_type y) {
  return (x | y) ;
}

ATSinline()
ats_ulint_type
atspre_lxor_ulint_ulint (ats_ulint_type x, ats_ulint_type y) {
  return (x ^ y) ;
}

ATSinline()
ats_ulint_type
atspre_lsl_ulint_int1 (ats_ulint_type i, ats_int_type n) {
  return i << n ;
}

ATSinline()
ats_ulint_type
atspre_lsr_ulint_int1 (ats_ulint_type i, ats_int_type n) {
  return i >> n ;
}

/* ****** ****** */

//
// long long integers
//

/* ****** ****** */

ATSinline()
ats_llint_type
atspre_llint_of_int
  (ats_int_type i) { return ((ats_llint_type)i) ; }
// end of [atspre_llint_of_int]

//
// arithmetic functions and comparison functions
//

ATSinline()
ats_llint_type
atspre_abs_llint (ats_llint_type i) {
  return (i >= 0 ? i : -i) ;
}

ATSinline()
ats_llint_type
atspre_neg_llint (ats_llint_type i) {
  return (-i) ;
}

ATSinline()
ats_llint_type
atspre_succ_llint (ats_llint_type i) { return (i + 1) ; }

ATSinline()
ats_llint_type
atspre_pred_llint (ats_llint_type i) { return (i - 1) ; }

ATSinline()
ats_llint_type
atspre_add_llint_llint (
  ats_llint_type i1
, ats_llint_type i2
) {
  return (i1 + i2) ;
}

ATSinline()
ats_llint_type
atspre_sub_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 - i2) ;
}

ATSinline()
ats_llint_type
atspre_mul_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 * i2) ;
}

ATSinline()
ats_llint_type
atspre_div_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 / i2) ;
}

ATSinline()
ats_llint_type
atspre_mod_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 % i2) ;
}

ATSinline()
ats_bool_type
atspre_lt_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 < i2) ;
}

ATSinline()
ats_bool_type
atspre_lte_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 <= i2) ;
}

ATSinline()
ats_bool_type
atspre_gt_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 > i2) ;
}

ATSinline()
ats_bool_type
atspre_gte_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 >= i2) ;
}

ATSinline()
ats_bool_type
atspre_eq_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 == i2) ;
}

ATSinline()
ats_bool_type
atspre_neq_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 != i2) ;
}

// compare, max and min

ATSinline()
ats_int_type
atspre_compare_llint_llint
  (ats_llint_type i1, ats_llint_type i2) {
  if (i1 < i2) return (-1) ;
  else if (i1 > i2) return ( 1) ;
  else return (0) ;
}

ATSinline()
ats_llint_type
atspre_max_llint_llint (
  ats_llint_type i1, ats_llint_type i2
) {
  return (i1 >= i2 ? i1 : i2) ;
} // end of [atspre_max_llint_llint]

ATSinline()
ats_llint_type
atspre_min_llint_llint (
  ats_llint_type i1, ats_llint_type i2
) {
  return (i1 <= i2 ? i1 : i2) ;
} // end of [atspre_min_llint_llint]

/* ****** ****** */

//
// unsigned long long integers
//

/* ****** ****** */

ATSinline()
ats_ullint_type
atspre_ullint_of_int
  (ats_int_type i) { return ((ats_ullint_type)i) ; }
// end of [atspre_ullint_of_int]

ATSinline()
ats_ullint_type
atspre_ullint_of_uint
  (ats_uint_type u) { return ((ats_ullint_type)u) ; }
// end of [atspre_ullint_of_uint]

/* ****** ****** */

ATSinline()
ats_ullint_type
atspre_succ_ullint (ats_ullint_type i) { return (i + 1) ; }

ATSinline()
ats_ullint_type
atspre_pred_ullint (ats_ullint_type i) { return (i - 1) ; }

ATSinline()
ats_ullint_type
atspre_add_ullint_ullint (
  ats_ullint_type i1, ats_ullint_type i2
) {
  return (i1 + i2) ;
} // end of [atspre_add_ullint_ullint]

ATSinline()
ats_ullint_type
atspre_sub_ullint_ullint (
  ats_ullint_type i1, ats_ullint_type i2
) {
  return (i1 - i2) ;
} // end of [atspre_sub_ullint_ullint]

ATSinline()
ats_ullint_type
atspre_mul_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 * i2) ;
}

ATSinline()
ats_ullint_type
atspre_div_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 / i2) ;
}

ATSinline()
ats_ullint_type
atspre_mod_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 % i2) ;
}

ATSinline()
ats_bool_type
atspre_lt_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 < i2) ;
}

ATSinline()
ats_bool_type
atspre_lte_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 <= i2) ;
}

ATSinline()
ats_bool_type
atspre_gt_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 > i2) ;
}

ATSinline()
ats_bool_type
atspre_gte_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 >= i2) ;
}

ATSinline()
ats_bool_type
atspre_eq_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 == i2) ;
}

ATSinline()
ats_bool_type
atspre_neq_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 != i2) ;
}

//
// compare, max and min
//

ATSinline()
ats_int_type
atspre_compare_ullint_ullint
  (ats_ullint_type i1, ats_ullint_type i2) {
  if (i1 < i2) return (-1) ;
  else if (i1 > i2) return ( 1) ;
  else return (0) ;
} // end of [atspre_compare_ullint_ullint]

ATSinline()
ats_ullint_type
atspre_max_ullint_ullint (
  ats_ullint_type i1
, ats_ullint_type i2
) {
  return (i1 >= i2 ? i1 : i2) ;
}

ATSinline()
ats_ullint_type
atspre_min_ullint_ullint (
  ats_ullint_type i1
, ats_ullint_type i2
) {
  return (i1 <= i2 ? i1 : i2) ;
}

/* ****** ****** */

#endif /* ATSCTRB_LINUX_INTEGER_CATS */

/* end of [integer.cats] */
