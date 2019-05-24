(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2009 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "symbol.sats"; staload "token.sats"

(* ****** ****** *)

abstype rulerhs_t (int) // boxed type for the right hand sides of rules
typedef rulerhs_t = [n:nat] rulerhs_t (n)
typedef rulerhslst = List (rulerhs_t)

(* ****** ****** *)

// implemented in [symbol.dats]
fun symbol_rulerhslst_get (sym: symbol_t):<> rulerhslst
  = "atsyacc_symbol_rulerhslst_get"

// implemented in [symbol.dats]
fun symbol_rulerhslst_set (sym: symbol_t, rhss: rulerhslst): void
  = "atsyacc_symbol_rulerhslst_set"

fun symbol_rulerhslst_postpend
  (sym: symbol_t, rhss: rulerhslst): void

(* ****** ****** *)

fun rulerhs_num_get {n:nat} (rhs: rulerhs_t n):<> int
fun rulerhs_nsym_get {n:nat} (rhs: rulerhs_t n):<> int n

typedef symarr (n:int) = array (symbol_t, n)
fun rulerhs_symarr_get {n:nat} (rhs: rulerhs_t n): symarr n

fun rulerhs_make {n:nat} (
  num: int
, nsym: int n, symarr: array (symbol_t, n)
, prec: tokenopt, ext: tokenopt
) : rulerhs_t (n)

(* ****** ****** *)

fun the_rulelhslst_add (x: symbol_t): void

fun the_rulelhslst_get (): List symbol_t
fun the_rulelhslst_set (xs: List symbol_t): void

(* ****** ****** *)

fun the_nrulerhs_get (): int

(* ****** ****** *)

fun fprint_rulerhs {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, rhs: rulerhs_t): void

fun fprint_rulelhsrhss {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, x: symbol_t): void

fun fprint_rulelhsrhsslst {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, xs: List symbol_t): void

(* ****** ****** *)

fun the_start_rule_set (): void
fun the_start_symbol_get (): symbol_t
fun the_start_symbol_set (sym: symbol_t): void

(* ****** ****** *)

(* end of [grammar.dats] *)
