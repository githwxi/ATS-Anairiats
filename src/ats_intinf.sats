(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
*)

(* ****** ****** *)

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December 2007

(* ****** ****** *)

%{#
#include "ats_intinf.cats"
%} // end of [%{#]

(* ****** ****** *)

abstype intinf_t // boxed types

fun intinf_make_int (i: int): intinf_t
fun intinf_make_string (str: string): intinf_t
fun intinf_make_stringsp (str: string): intinf_t

(* ****** ****** *)

fun intinf_get_int (i: intinf_t): int

(* ****** ****** *)

fun lt_intinf_int
  (_: intinf_t, _: int): bool = "atsopt_lt_intinf_int"
overload < with lt_intinf_int

fun lte_intinf_int
  (_: intinf_t, _: int): bool = "atsopt_lte_intinf_int"
overload <= with lte_intinf_int

fun lt_intinf_intinf
  (_: intinf_t, _: intinf_t): bool = "atsopt_lt_intinf_intinf"
overload < with lt_intinf_intinf

fun lte_intinf_intinf
  (_: intinf_t, _: intinf_t): bool = "atsopt_lte_intinf_intinf"
overload <= with lte_intinf_intinf

(* ****** ****** *)

fun gt_intinf_int
  (_: intinf_t, _: int): bool = "atsopt_gt_intinf_int"
overload > with gt_intinf_int

fun gte_intinf_int
  (_: intinf_t, _: int): bool = "atsopt_gte_intinf_int"
overload >= with gte_intinf_int

fun gt_intinf_intinf
  (_: intinf_t, _: intinf_t): bool = "atsopt_gt_intinf_intinf"
overload > with gt_intinf_intinf

fun gte_intinf_intinf
  (_: intinf_t, _: intinf_t): bool = "atsopt_gte_intinf_intinf"
overload >= with gte_intinf_intinf

(* ****** ****** *)

fun eq_int_intinf
  (_: int, _: intinf_t): bool = "atsopt_eq_int_intinf"
overload = with eq_int_intinf

fun eq_intinf_int
  (_: intinf_t, _: int): bool = "atsopt_eq_intinf_int"
overload = with eq_intinf_int

fun eq_intinf_intinf
  (_: intinf_t, _: intinf_t): bool = "atsopt_eq_intinf_intinf"
overload = with eq_intinf_intinf

fun neq_intinf_int
  (_: intinf_t, _: int): bool = "atsopt_neq_intinf_int"
overload <> with neq_intinf_int

fun neq_intinf_intinf
  (_: intinf_t, _: intinf_t): bool = "atsopt_neq_intinf_intinf"
overload <> with neq_intinf_intinf

(* ****** ****** *)

fun compare_intinf_intinf
  (_: intinf_t, _: intinf_t): Sgn = "atsopt_compare_intinf_intinf"
overload compare with compare_intinf_intinf

(* ****** ****** *)

fun neg_intinf
  (_: intinf_t): intinf_t = "atsopt_neg_intinf"
overload ~ with neg_intinf

fun add_intinf_intinf
  (_: intinf_t, _: intinf_t): intinf_t = "atsopt_add_intinf_intinf"
overload + with add_intinf_intinf

fun sub_intinf_intinf
  (_: intinf_t, _: intinf_t): intinf_t = "atsopt_sub_intinf_intinf"
overload - with sub_intinf_intinf

fun mul_intinf_intinf
  (_: intinf_t, _: intinf_t): intinf_t = "atsopt_mul_intinf_intinf"
overload * with mul_intinf_intinf

fun div_intinf_intinf
  (_: intinf_t, _: intinf_t): intinf_t = "atsopt_div_intinf_intinf"
overload / with div_intinf_intinf

(* ****** ****** *)

fun fprint_intinf {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, i: intinf_t): void
overload fprint with fprint_intinf

fun print_intinf (i: intinf_t): void
overload print with print_intinf
fun prerr_intinf (i: intinf_t): void
overload prerr with prerr_intinf

(* ****** ****** *)

fun tostring_intinf
  (i: intinf_t): string = "atsopt_tostring_intinf"
overload tostring with tostring_intinf

(* ****** ****** *)

(* end of [ats_intinf.sats] *)
