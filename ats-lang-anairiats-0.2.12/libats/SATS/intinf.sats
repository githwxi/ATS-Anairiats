(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

//
// HX-2010-02-06:
//
// infinite precision integers based on the gmp package; the primary purpose
// of [intinf] is for doing quick demo involving large numbers. If you need
// full-fledged support for large numbers, please use the API for GMP in ATS
// directly:
//
// $ATSHOME/libc/SATS/gmp.sats
//

(* ****** ****** *)

%{#
#include "libats/CATS/intinf.cats"
%} // end of [%{#]

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)
//
// HX: a linear type of unspecified size
//
absviewtype intinf (int)
viewtypedef Intinf = [i:int] intinf (i)

(* ****** ****** *)

symintr intinf_make

fun intinf_make_int
  {i:int} (i: int i):<> intinf (i)
overload intinf_make with intinf_make_int

fun intinf_make_lint
  {i:int} (i: lint i):<> intinf (i)
overload intinf_make with intinf_make_lint

fun intinf_make_llint
  {i:int} (i: llint i):<> intinf (i)
overload intinf_make with intinf_make_llint

fun intinf_make_double
  (d: double):<> Intinf // [d] should be integral
overload intinf_make with intinf_make_double

fun intinf_make_string
  (rep: string):<> Intinf
overload intinf_make with intinf_make_string

fun intinf_make_intinf
  {i:int} (i: !intinf (i)):<> intinf (i)
overload intinf_make with intinf_make_intinf

(* ****** ****** *)

fun intinf_free (x: Intinf): void

(* ****** ****** *)

fun intinf_get_int // HX: this is unsafe because of potential
  {n:int} (n: !intinf n): int n = "mac#atslib_mpz_get_int" // overflow
// end of [intinf_get_int]

(* ****** ****** *)

symintr fprint_intinf

fun fprint0_intinf
 {i:int} (out: FILEref, i: !intinf i): void
fun fprint1_intinf {m:file_mode} {i:int}
  (pf: file_mode_lte (m, w) | fil: &FILE m, i: !intinf i): void
overload fprint_intinf with fprint0_intinf
overload fprint_intinf with fprint1_intinf

fun print_intinf {i:int} (i: !intinf i): void
overload print with print_intinf

symintr fprint_intinf_base
fun fprint0_intinf_base {i:int} (
  out: FILEref, b: intBtw (2, 36+1), i: !intinf i
) : void // end of [fprint0_intinf_base]
fun fprint1_intinf_base {m:file_mode} {i:int} (
  pf: file_mode_lte (m, w) | fil: &FILE m, b: intBtw (2, 36+1), i: !intinf i
) : void // end of [fprint1_intinf_base]
overload fprint_intinf_base with fprint0_intinf_base
overload fprint_intinf_base with fprint1_intinf_base

fun print_intinf_base
  {i:int} (b: intBtw (2, 36+1), i: !intinf i): void
overload print with print_intinf_base

(* ****** ****** *)

fun pred_intinf {i:int} (i: !intinf i): intinf (i-1)
  
overload pred with pred_intinf

fun succ_intinf {i:int} (i: !intinf i): intinf (i+1)
overload succ with succ_intinf

//

fun add_intinf_int {i,j:int}
  (i: !intinf i, j: int j): intinf (i+j)
overload + with add_intinf_int

fun add_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): intinf (i+j)
overload + with add_intinf_intinf

//

fun sub_intinf_int {i,j:int}
  (i: !intinf i, j: int j): intinf (i-j)
overload - with sub_intinf_int

fun sub_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): intinf (i-j)
overload - with sub_intinf_intinf

//

fun mul_int_intinf {m,n:int}
  (m: int m, n: !intinf n): [p:int] (MUL (m, n, p) | intinf p)
overload * with mul_int_intinf

fun mul_intinf_int {m,n:int}
  (m: !intinf m, n: int n): [p:int] (MUL (m, n, p) | intinf p)
overload * with mul_intinf_int

fun mul_intinf_intinf {m,n:int}
  (m: !intinf m, n: !intinf n): [p:int] (MUL (m, n, p) | intinf p)
overload * with mul_intinf_intinf

(* ****** ****** *)

fun square_intinf
  {n:int} (n: !intinf n): [p:int] (MUL (n, n, p) | intinf p)
overload square with square_intinf

(* ****** ****** *)

//
// fdiv: floor division: round toward -infinity
//
fun fdiv_intinf_int
  {m,n:int | n > 0} (m: !intinf m, n: int n)
  : [q,r:int | 0 <= r; r < n] (MUL (q, n, m-r) | intinf q)
  = "atslib_fdiv_intinf_int"
overload / with fdiv_intinf_int

//
// fmod: floor division: round toward -infinity
//
fun fmod_intinf_int
  {m,n:int | n > 0} (m: !intinf m, n: int n)
  : [q,r:int | 0 <= r; r < n] (MUL (q, n, m-r) | int r)
overload mod with fmod_intinf_int

(* ****** ****** *)

fun lt_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i < j)
  = "atslib_lt_intinf_int"
overload < with lt_intinf_int

fun lt_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i < j)
  = "atslib_lt_intinf_intinf"
overload < with lt_intinf_intinf

//

fun lte_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i <= j)
  = "atslib_lte_intinf_int"
overload <= with lte_intinf_int

fun lte_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i <= j)
  = "atslib_lte_intinf_intinf"
overload <= with lte_intinf_intinf

//

fun gt_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i > j)
  = "atslib_gt_intinf_int"
overload > with gt_intinf_int

fun gt_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i > j)
  = "atslib_gt_intinf_intinf"
overload > with gt_intinf_intinf

//

fun gte_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i >= j)
  = "atslib_gte_intinf_int"
overload >= with gte_intinf_int

fun gte_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i >= j)
  = "atslib_gte_intinf_intinf"
overload >= with gte_intinf_intinf

//

fun eq_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i == j)
  = "atslib_eq_intinf_int"
overload = with eq_intinf_int

fun eq_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i == j)
  = "atslib_eq_intinf_intinf"
overload = with eq_intinf_intinf

//

fun neq_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i <> j)
  = "atslib_neq_intinf_int"
overload <> with neq_intinf_int

fun neq_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i <> j)
  = "atslib_neq_intinf_intinf"
overload <> with neq_intinf_intinf

//

fun compare_intinf_int {i,j:int}
  (i: !intinf i, j: int j): [k:int | sgn_r (i-j, k)] int k
  = "atslib_compare_intinf_int"
overload compare with compare_intinf_int

fun compare_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): [k:int | sgn_r (i-j, k)] int k
  = "atslib_compare_intinf_intinf"
overload compare with compare_intinf_intinf

(* ****** ****** *)

(* end of [intinf.sats] *)
