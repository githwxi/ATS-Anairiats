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
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// integral numbers

absviewt@ype mpz_viewt0ype = $extype "ats_mpz_viewt0ype"
stadef mpz_vt = mpz_viewt0ype

// rational numbers

absviewt@ype mpq_viewt0ype = $extype "ats_mpq_viewt0ype"
stadef mpq_vt = mpq_viewt0ype

(* ****** ****** *)

// [x] is initialized with 0
fun mpz_init
  (x: &mpz_vt? >> mpz_vt):<> void = "mac#atslib_mpz_init"
// end of [mpz_init]

// [x] is cleared
fun mpz_clear
  (x: &mpz_vt >> mpz_vt?):<> void = "mac#atslib_mpz_clear"
// end of [mpz_clear]

(* ****** ****** *)

fun mpz_get_int
  (x: &mpz_vt):<> int = "mac#atslib_mpz_get_int" // macro!
// end of [mpz_get_int]

fun mpz_get_str
  {i:int | 2 <= i; i <= 36} (base: int i, x: &mpz_vt): String
  = "atslib_mpz_get_str" // function!
// end of [mpz_get_str]

(* ****** ****** *)

symintr mpz_set

// [x] := [y]
fun mpz_set_mpz
  (x: &mpz_vt, y: &mpz_vt):<> void = "mac#atslib_mpz_set_mpz"
overload mpz_set with mpz_set_mpz

// [x] := [y]
fun mpz_set_int (x: &mpz_vt, y: int):<> void = "mac#atslib_mpz_set_int"
overload mpz_set with mpz_set_int

(* ****** ****** *)

symintr mpz_init_set

// [x] := [y]
fun mpz_init_set_mpz (
  x: &mpz_vt? >> mpz_vt, y: &mpz_vt
) :<> void
  = "mac#atslib_mpz_init_set_mpz"
overload mpz_init_set with mpz_init_set_mpz

// [x] := [y]
fun mpz_init_set_int (
  x: &mpz_vt? >> mpz_vt, y: int
) :<> void
  = "mac#atslib_mpz_init_set_int"
overload mpz_init_set with mpz_init_set_int

// the function returns 0 if the string is valid, or -1 otherwise.
fun mpz_init_set_str_err
  {i:int | 2 <= i; i <= 62}
  (x: &mpz_vt? >> mpz_vt, s: string, base: int i):<> int
  = "atslib_mpz_init_set_str_err" // function!

// the function exits the string is invalid.
fun mpz_init_set_str_exn
  {i:int | 2 <= i; i <= 62}
  (x: &mpz_vt? >> mpz_vt, s: string, base: int i):<> void
  = "atslib_mpz_init_set_str_exn" // function!

(* ****** ****** *)

#define sixtythree 63
fun mpz_out_str_err
  {m:file_mode} (
  pf_mode: file_mode_lte (m, w)
| file: &FILE m, base: intBtw (2, sixtythree), x: &mpz_vt
) : int
  = "mac#atslib_mpz_out_str_err"
// end of [mpz_out_str_err]

fun mpz_out_str_exn
  {m:file_mode} (
  pf_mode: file_mode_lte (m, w)
| file: &FILE m, base: intBtw (2, sixtythree), x: &mpz_vt
) : void = "atslib_mpz_out_str_exn"
// end of [mpz_out_str_exn]

(* ****** ****** *)

// negation

symintr mpz_neg

// [x] := -[y]
fun mpz_neg_2
  (x: &mpz_vt, y: &mpz_vt):<> void = "mac#atslib_mpz_neg_2"
overload mpz_neg with mpz_neg_2

// [x] := -[x]
fun mpz_neg_1 (x: &mpz_vt):<> void = "mac#atslib_mpz_neg_1"
overload mpz_neg with mpz_neg_1

(* ****** ****** *)

//
// addition
//

symintr mpz_add

// [x] := [y] + [z]
fun mpz_add_mpz_3 (
  x: &mpz_vt, y: &mpz_vt, z: &mpz_vt
) :<> void
  = "mac#atslib_mpz_add_mpz_3"
overload mpz_add with mpz_add_mpz_3

fun mpz_add_int_3 (
  x: &mpz_vt, y: &mpz_vt, z: int
) :<> void
  = "mac#atslib_mpz_add_int_3"
overload mpz_add with mpz_add_int_3

// [x] := [x] + [y]
fun mpz_add_mpz_2 (
  x: &mpz_vt, y: &mpz_vt
) :<> void
  = "mac#atslib_mpz_add_mpz_2"
overload mpz_add with mpz_add_mpz_2

fun mpz_add_int_2
  (x: &mpz_vt, y: int):<> void = "mac#atslib_mpz_add_int_2"
overload mpz_add with mpz_add_int_2

(* ****** ****** *)

//
// subtraction
//

symintr mpz_sub

// [x] := [y] - [z]
fun mpz_sub_mpz_3 (
  x: &mpz_vt, y: &mpz_vt, z: &mpz_vt
) :<> void = "mac#atslib_mpz_sub_mpz_3"
overload mpz_sub with mpz_sub_mpz_3

fun mpz_sub_int_3 (
  x: &mpz_vt, y: &mpz_vt, z: int
) :<> void = "mac#atslib_mpz_sub_int_3"
overload mpz_sub with mpz_sub_int_3

// [x] := [x] - [y]
fun mpz_sub_mpz_2 (
  x: &mpz_vt, y: &mpz_vt
) :<> void = "mac#atslib_mpz_sub_mpz_2"
overload mpz_sub with mpz_sub_mpz_2

fun mpz_sub_int_2
  (x: &mpz_vt, y: int):<> void = "mac#atslib_mpz_sub_int_2"
overload mpz_sub with mpz_sub_int_2

(* ****** ****** *)

//
// multiplication
//

symintr mpz_mul

// [x] := [y] * [z]
fun mpz_mul_mpz_3
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt)
  :<> void = "mac#atslib_mpz_mul_mpz_3"
overload mpz_mul with mpz_mul_mpz_3

fun mpz_mul_int_3 (
  x: &mpz_vt, y: &mpz_vt, z: int
) :<> void = "mac#atslib_mpz_mul_int_3"
overload mpz_mul with mpz_mul_int_3

// [x] := [x] * [y]
fun mpz_mul_mpz_2
  (x: &mpz_vt, y: &mpz_vt):<> void = "mac#atslib_mpz_mul_mpz_2"
overload mpz_mul with mpz_mul_mpz_2

fun mpz_mul_int_2
  (x: &mpz_vt, y: int):<> void = "mac#atslib_mpz_mul_int_2"
overload mpz_mul with mpz_mul_int_2

// [x] := [x] * [x]
fun mpz_mul_mpz_1 (x: &mpz_vt):<> void = "mac#atslib_mpz_mul_mpz_1"
overload mpz_mul with mpz_mul_mpz_1

(* ****** ****** *)

//
// comparison
//

symintr mpz_cmp

fun mpz_cmp_mpz
  (x: &mpz_vt, y: &mpz_vt):<> Sgn = "mac#atslib_mpz_cmp_mpz"
overload mpz_cmp with mpz_cmp_mpz

fun mpz_cmp_int (x: &mpz_vt, y: int):<> Sgn = "mac#atslib_mpz_cmp_int"
overload mpz_cmp with mpz_cmp_int

(* ****** ****** *)

fun fprint_mpz
  {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, x: &mpz_vt
) :<!exnref> void
  = "atslib_fprint_mpz"
overload fprint with fprint_mpz

fun print_mpz
  (x: &mpz_vt) :<!ref> void = "atslib_print_mpz"
overload print with print_mpz

fun prerr_mpz
  (x: &mpz_vt) :<!ref> void = "atslib_prerr_mpz"
overload prerr with prerr_mpz

(* ****** ****** *)

(* end of [libc_sats_gmp.sats] *)
