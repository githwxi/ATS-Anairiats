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

(* Mainly for testing exhaustiveness of pattern mattching  *)

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

abstype intinfset_t // boxed type

fun intinflst_of_intinfset (xs: intinfset_t): List intinf_t

datatype p2atcst =
  | P2TCany
  | P2TCbool of bool // boolean pattern
  | P2TCchar of char // character pattern
    // constructor pattern
  | P2TCcon of (d2con_t, p2atcstlst)
  | P2TCempty
  | P2TCfloat of string
  | P2TCint of intinf_t
  | P2TCintc of intinfset_t
    // record pattern
  | P2TCrec of (int(*recknd*), labp2atcstlst)
  | P2TCstring of string // string pattern
// end of [p2atcst]

and labp2atcstlst =
  | LABP2ATCSTLSTnil
  | LABP2ATCSTLSTcons of (lab_t, p2atcst, labp2atcstlst)
// end of [labp2atcstlst]

where p2atcstlst (n:int) = list (p2atcst, n)
and p2atcstlst = [n:nat] p2atcstlst n
and p2atcstlst_vt (n:int) = list_vt (p2atcst, n)
and p2atcstlst_vt = [n:nat] p2atcstlst_vt n
and p2atcstlstlst (n:int) = List (p2atcstlst n)
and p2atcstlstlst = [n:nat] p2atcstlstlst n

and labp2atcstlstlst = List labp2atcstlst

(* ****** ****** *)

fun p2atcst_of_p2at (_: p2at): p2atcst
fun p2atcstlst_of_p2atlst {n:nat} (_: p2atlst n): p2atcstlst n

(* ****** ****** *)

fun fprint_p2atcst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: p2atcst): void

fun fprint_p2atcstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: p2atcstlst): void

fun fprint_p2atcstlstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: p2atcstlstlst): void

overload fprint with fprint_p2atcst
overload fprint with fprint_p2atcstlst
overload fprint with fprint_p2atcstlstlst

fun fprint_labp2atcstlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, _: labp2atcstlst): void
// end of [fprint_labp2atcstlst]

overload fprint with fprint_labp2atcstlst

fun print_p2atcst (_: p2atcst): void
fun prerr_p2atcst (_: p2atcst): void

overload print with print_p2atcst
overload prerr with prerr_p2atcst

fun print_p2atcstlst (_: p2atcstlst): void
fun prerr_p2atcstlst (_: p2atcstlst): void

overload print with print_p2atcstlst
overload prerr with prerr_p2atcstlst

fun print_p2atcstlstlst (_: p2atcstlstlst): void
fun prerr_p2atcstlstlst (_: p2atcstlstlst): void

overload print with print_p2atcstlstlst
overload prerr with prerr_p2atcstlstlst

(* ****** ****** *)

fun p2atcst_complement (_: p2atcst): p2atcstlst

fun p2atcstlst_complement {n:nat} (_: p2atcstlst n): p2atcstlstlst n

fun labp2atcstlst_complement (_: labp2atcstlst): labp2atcstlstlst

//

fun c2lau_pat_complement {n:nat} (_: c2lau n): p2atcstlstlst n

(* ****** ****** *)

fun p2atcst_intersect_test (_: p2atcst, _: p2atcst): bool

fun p2atcstlst_intersect_test {n:nat}
  (_: list (p2atcst, n), _: list (p2atcst, n)): bool

fun labp2atcstlst_intersect_test (_: labp2atcstlst, _: labp2atcstlst): bool

(* ****** ****** *)

fun p2atcst_difference (_: p2atcst, _: p2atcst): p2atcstlst

fun p2atcstlst_difference {n:nat}
  (_: list (p2atcst, n), _: list (p2atcst, n)): List (list (p2atcst, n))

fun labp2atcstlst_difference
  (_: labp2atcstlst, _: labp2atcstlst): List (labp2atcstlst)

(* ****** ****** *)

(* end of [ats_patcst2.sats] *)
