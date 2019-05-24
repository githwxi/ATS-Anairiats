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

(* ats_label: handling labels *)

(* ****** ****** *)

staload "ats_symbol.sats"

(* ****** ****** *)

abstype label_t // boxed type

(* ****** ****** *)

fun label_make_int (i: int): label_t
fun label_make_string (str: string): label_t
fun label_make_sym (sym: symbol_t): label_t

fun label_get_int (l: label_t): Option_vt int
fun label_get_sym (l: label_t): Option_vt symbol_t

(* ****** ****** *)

fun lt_label_label (l1: label_t, l2: label_t):<> bool
fun lte_label_label (l1: label_t, l2: label_t):<> bool

overload < with lt_label_label
overload <= with lte_label_label

fun gt_label_label (l1: label_t, l2: label_t):<> bool
fun gte_label_label (l1: label_t, l2: label_t):<> bool

overload > with gt_label_label
overload >= with gte_label_label

fun eq_label_label (l1: label_t, l2: label_t):<> bool
fun neq_label_label (l1: label_t, l2: label_t):<> bool

overload = with eq_label_label
overload <> with neq_label_label

fun compare_label_label (l1: label_t, l2: label_t):<> Sgn

overload compare with compare_label_label

(* ****** ****** *)

fun fprint_label {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, l: label_t): void

overload fprint with fprint_label

fun print_label (l: label_t): void
fun prerr_label (l: label_t): void

overload print with print_label
overload prerr with prerr_label

(* ****** ****** *)

fun labeled_list_sort {a:type} {n:nat}
  (lxs: list ('(label_t, a), n)): list ('(label_t, a), n)
// end of [labeled_list_sort]

(* ****** ****** *)

(* end of [ats_label.sats] *)
