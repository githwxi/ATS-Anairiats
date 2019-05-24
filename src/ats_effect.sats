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
// Time: August 2007
//
(* ****** ****** *)

staload Loc = "ats_location.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

typedef effect_t = $Syn.effect_t
typedef effectlst = $Syn.effectlst
abst@ype effset_t = $extype "ats_uint_type"

(* ****** ****** *)

val effect_exn : effect_t
val effect_ntm : effect_t
val effect_ref : effect_t
(*
val effect_wrt : effect_t // not supported
*)

val effectlst_all : effectlst

fun eq_effect_effect (eff1: effect_t, eff2: effect_t): bool
overload = with eq_effect_effect

fun fprint_effect {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, eff: effect_t): void
  = "atsopt_fprint_effect"
overload fprint with fprint_effect

fun fprint_effectlst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, eff: effectlst): void
overload fprint with fprint_effectlst

fun print_effect (eff: effect_t): void
fun prerr_effect (eff: effect_t): void

overload print with print_effect
overload prerr with prerr_effect

(* ****** ****** *)

typedef effvar = $Syn.i0de
typedef effvarlst = List effvar

datatype effcst =
  | EFFCSTall | EFFCSTnil | EFFCSTset of (effset_t, effvarlst)
// end of [effcst]

(* ****** ****** *)

val effset_all: effset_t and effset_nil: effset_t

fun eq_effset_effset (efs1: effset_t, efs2: effset_t): bool
overload = with eq_effset_effset

fun fprint_effset {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, efs: effset_t): void
  = "atsopt_fprint_effset"

fun effset_add (efs: effset_t, eff: effect_t): effset_t
  = "atsopt_effset_add"

fun effset_del (efs: effset_t, eff: effect_t): effset_t
  = "atsopt_effset_del"

fun effset_contain (efs: effset_t, eff: effect_t): bool
  = "atsopt_effset_contain"

fun effset_union (efs1: effset_t, efs2: effset_t): effset_t
  = "atsopt_effset_union"

fun effset_subset (efs1: effset_t, efs2: effset_t): bool
  = "atsopt_effset_subset"

(* ****** ****** *)

fun fprint_effcst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, effc: effcst): void
overload fprint with fprint_effcst

fun print_effcst (efc: effcst): void
overload print with print_effcst
fun prerr_effcst (efc: effcst): void
overload prerr with prerr_effcst

(* ****** ****** *)

fun effcst_contain (efc: effcst, eff: effect_t): bool
fun effcst_contain_ntm (efc: effcst): bool

(* ****** ****** *)

fun e0fftaglst_tr
  (tags: $Syn.e0fftaglst): @($Syn.funcloopt, int, int, effcst)
// end of [e0fftaglst_tr]

(* ****** ****** *)

(* end of [ats_effect.sats] *)
