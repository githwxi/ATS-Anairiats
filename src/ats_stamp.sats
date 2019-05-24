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
// Time: October 2007

(* ****** ****** *)

staload Cnt = "ats_counter.sats"

(* ****** ****** *)

abst@ype stamp_t = $Cnt.count_t

(* ****** ****** *)

fun lt_stamp_stamp (s1: stamp_t, s2: stamp_t):<> bool
overload < with lt_stamp_stamp

fun lte_stamp_stamp (s1: stamp_t, s2: stamp_t):<> bool
overload <= with lte_stamp_stamp

fun eq_stamp_stamp (s1: stamp_t, s2: stamp_t):<> bool
overload = with eq_stamp_stamp

fun neq_stamp_stamp (s1: stamp_t, s2: stamp_t):<> bool
overload <> with neq_stamp_stamp

fun compare_stamp_stamp (s1: stamp_t, s2: stamp_t):<> Sgn
overload compare with compare_stamp_stamp

(* ****** ****** *)

fun fprint_stamp {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | fil: &FILE m, s: stamp_t): void
overload fprint with fprint_stamp

fun print_stamp (s: stamp_t): void
fun prerr_stamp (s: stamp_t): void

fun tostring_stamp (s: stamp_t): string

(* ****** ****** *)

fun s2rtdat_stamp_make (): stamp_t
fun s2cst_stamp_make (): stamp_t
fun s2var_stamp_make (): stamp_t
fun s2Var_stamp_make (): stamp_t
fun s2exp_struct_stamp_make (): stamp_t
fun s2exp_union_stamp_make (): stamp_t

fun d2con_stamp_make (): stamp_t
fun d2cst_stamp_make (): stamp_t
fun d2mac_stamp_make (): stamp_t
fun d2var_stamp_make (): stamp_t

(* ****** ****** *)

fun funlab_stamp_make (): stamp_t
fun tmplab_stamp_make (): stamp_t
fun tmpvar_stamp_make (): stamp_t

(* ****** ****** *)

(* end of [ats_stamp.sats] *)
