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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: July 2007
//
(* ****** ****** *)

staload
Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t

(* ****** ****** *)

abst@ype prec_t = int (* precedence type *)

(* ****** ****** *)

val neginf_prec : prec_t // lowest legal precedence value
val posinf_prec : prec_t // highest legal precedence value

(* ****** ****** *)

val app_prec : prec_t

(* ****** ****** *)

val select_prec : prec_t

(* ****** ****** *)

val backslash_prec : prec_t
val infixtemp_prec : prec_t // for temp infix status

(* ****** ****** *)

val exi_prec_sta : prec_t
and uni_prec_sta : prec_t

val delay_prec_dyn : prec_t

val dynload_prec_dyn : prec_t

val exist_prec_dyn : prec_t

val ptrof_prec_dyn : prec_t

(* ****** ****** *)

val foldat_prec_dyn : prec_t
val freeat_prec_dyn : prec_t
val viewat_prec_dyn : prec_t

(* ****** ****** *)

val invar_prec_sta : prec_t

val qmark_prec_sta : prec_t

val qmarkbang_prec_sta : prec_t

val r0ead_prec_sta : prec_t

val trans_prec_sta : prec_t

(* ****** ****** *)

val crypt_prec_dyn : prec_t

val deref_prec_dyn : prec_t

(* ****** ****** *)

fun int_of_prec (p: prec_t): int
fun prec_make_int (i: int): prec_t

fun precedence_inc (p: prec_t, i: int): prec_t
fun precedence_dec (p: prec_t, i: int): prec_t

(* ****** ****** *)

fun compare_prec_prec (p1: prec_t, p2: prec_t): Sgn
overload compare with compare_prec_prec

(* ****** ****** *)

datatype assoc = ASSOCnon | ASSOClft | ASSOCrgt

(* ****** ****** *)

(*
// HX-2011-02-13:
// it is exported mainly for pretty printing
*)
datatype fxty =
  | FXTYnon
  | FXTYinf of (prec_t, assoc)
  | FXTYpre of prec_t
  | FXTYpos of prec_t
// end of [fxty]

(* ****** ****** *)

val fxty_non : fxty
fun fxty_inf (p: prec_t, a: assoc): fxty
fun fxty_pre (p: prec_t): fxty
fun fxty_pos (p: prec_t): fxty

(* ****** ****** *)

val deref_fixity_dyn : fxty // for dereference
val selptr_fixity_dyn : fxty // for lab/ind selection

(* ****** ****** *)

fun fprint_fxty {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, fxty: fxty): void
// end of [fprint_fxty]

fun prerr_fxty (fxty: fxty): void
fun print_fxty (fxty: fxty): void

(* ****** ****** *)

fun fixity_get_prec (fxty: fxty): Option_vt (prec_t)

(* ****** ****** *)

datatype oper (a:type) = 
  | OPERinf (a) of (prec_t, assoc, (a, a) -<cloref1> item a)
  | OPERpre (a) of (prec_t, a -<cloref1> item a)
  | OPERpos (a) of (prec_t, a -<cloref1> item a)
// end of [oper]
        
and item (a: type) = ITEMatm (a) of a | ITEMopr (a) of oper a

fun oper_precedence {a:type} (opr: oper a): prec_t
fun oper_associativity {a:type} (opr: oper a): assoc

(* ****** ****** *)

fun item_app {a:type}
  (app: (a, a) -<cloref1> item a): item a
// end of [item_app]

(* ****** ****** *)

fun oper_make_backslash {a:type} (
  locf: a -> loc_t
, appf: (loc_t, a, loc_t, List a) -<cloref1> a
) : item a  // end of [oper_make_backslash]

fun oper_make {a:type} (
  locf: a -> loc_t
, appf: (loc_t, a, loc_t, List a) -<cloref1> a
, opr: a
, fxty: fxty
) : item a // end of [oper_make]

(* ****** ****** *)

fun fixity_resolve {a:type}
  (loc: loc_t, app: item a, xs: List (item a)): a
// end of [fixity_resolve]

(* ****** ****** *)

(* end of [ats_fixity.sats] *)
