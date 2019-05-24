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
// Time: July 2007

(* ****** ****** *)

(* ats_counter: counter implementation *)

(* ****** ****** *)

%{#
#include "ats_counter.cats"
%} // end of [%{#]

(* ****** ****** *)

abst@ype count_t = $extype "atsopt_count_type"
abstype counter_t // ref (count_t)

(* ****** ****** *)
//
fun lt_count_count (c1: count_t, c2: count_t):<> bool
overload < with lt_count_count
fun lte_count_count (c1: count_t, c2: count_t):<> bool
overload <= with lte_count_count
//
fun gt_count_count (c1: count_t, c2: count_t):<> bool
overload > with gt_count_count
fun gte_count_count (c1: count_t, c2: count_t):<> bool
overload >= with gte_count_count
//
fun eq_count_count (c1: count_t, c2: count_t):<> bool
overload = with eq_count_count
fun neq_count_count (c1: count_t, c2: count_t):<> bool
overload <> with neq_count_count
//
fun compare_count_count
  (c1: count_t, c2: count_t):<> Sgn = "atsopt_compare_count_count"
overload compare with compare_count_count
//
(* ****** ****** *)

fun count_hash
  (c: count_t):<> uInt = "atsopt_count_hash"
// end of [count_hash]

(* ****** ****** *)

fun fprint_count {m:file_mode} (
  pf: file_mode_lte (m, w) | out: &FILE m, c: count_t
) : void = "atsopt_fprint_count"
overload fprint with fprint_count

fun print_count (c: count_t): void
overload print with print_count
fun prerr_count (c: count_t): void
overload prerr with prerr_count

(* ****** ****** *)

fun tostring_count
  (cnt: count_t): string = "atsopt_tostring_count"
fun tostring_prefix_count
  (pre: string, cnt: count_t): string = "atsopt_tostring_prefix_count"

(* ****** ****** *)
//
// the following functions are implemented in [ats_counter.cats]
//
fun counter_make (): counter_t = "atsopt_counter_make"
//
fun counter_inc
  (cntr: counter_t): void = "atsopt_counter_inc"
fun counter_get
  (cntr: counter_t): count_t = "atsopt_counter_get"
fun counter_set
  (cntr: counter_t, cnt: count_t): void = "atsopt_counter_set"
fun counter_reset
  (cntr: counter_t): void = "atsopt_counter_reset"
//
fun counter_getinc
  (cntr: counter_t): count_t = "atsopt_counter_getinc"
fun counter_incget
  (cntr: counter_t): count_t = "atsopt_counter_incget"
//
(* ****** ****** *)

(* end of [ats_counter.sats] *)
