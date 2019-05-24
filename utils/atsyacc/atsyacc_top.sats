(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
**
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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
**
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "token.sats"
staload "symbol.sats"
staload "grammar.sats"

(* ****** ****** *)

// implemented in [atsyacc_lexer.lats]
fun atsyacc_lexer_token_get (): token = "atsyacc_lexer_token_get"

(* ****** ****** *)

// implemented in [atsyacc_parser.dats]
fun parse_from_stdin (): void
fun parse_from_filename (filename: string): void

(* ****** ****** *)

// implemented in [atsyacc_parser.dats]
fun the_rulelhsrhsslst_get (): List @(symbol_t, rulerhslst)

(* ****** ****** *)

// implemented in [atsyacc_nullfrstfllw.dats]
fun the_nullfrstfllw_table_gen (): void

(* ****** ****** *)

// implemented in [atsyacc_lrtable.dats]

abstype lrstate_t // for representing LR(1)-states

fun fprint_lrstate {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, st: lrstate_t): void

fun print_lrstate (st: lrstate_t): void
fun prerr_lrstate (st: lrstate_t): void

//

fun the_lrtable_gen (): void

typedef lrstatelst = List (lrstate_t)

fun the_lrstatelst_get (): lrstatelst
fun the_lrstatelst_initialize (): void

(* ****** ****** *)

fun theLHSarr_emit
  (out: FILEref, xs: List @(symbol_t, rulerhslst)): void

fun theLENarr_emit
  (out: FILEref, xs: List @(symbol_t, rulerhslst)): void

(* ****** ****** *)

(* end of [atsyacc_top.sats] *)
