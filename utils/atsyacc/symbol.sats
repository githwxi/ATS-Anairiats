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

abstype symbol_t // a boxed type for symbols

//

fun symbol_name_get (x: symbol_t): string

fun symbol_index_get (x: symbol_t): int = "atsyacc_symbol_index_get"

//

fun name_is_new (name: string): bool
fun symbol_find_name (name: string): Option_vt (symbol_t)

// terminal : knd = 0 / nonterm : knd = 1
datatype symkind = SYMKINDterm | SYMKINDnonterm

fun symbol_make_name (knd: symkind, name: string): symbol_t
fun symbol_make_newname (knd: symkind, name: string): symbol_t

//

val the_end_symbol : symbol_t // terminal

fun symbol_is_end (x: symbol_t): bool

val the_accept_symbol : symbol_t // nonterm

//

fun eq_symbol_symbol (x1: symbol_t, x2: symbol_t):<> bool
overload = with eq_symbol_symbol

fun neq_symbol_symbol (x1: symbol_t, x2: symbol_t):<> bool
overload <> with neq_symbol_symbol

fun compare_symbol_symbol (x1: symbol_t, x2: symbol_t):<> Sgn
overload compare with compare_symbol_symbol

//

fun fprint_symbol {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, _: symbol_t): void
  = "atsyacc_fprint_symbol"

fun print_symbol (_: symbol_t): void
fun prerr_symbol (_: symbol_t): void

//

fun symbol_is_term (x: symbol_t):<> bool // is terminal
fun symbol_is_nonterm (x: symbol_t):<> bool // is nonterminal

fun symbol_assoc_get (x: symbol_t): int
  = "atsyacc_symbol_assoc_get"
fun symbol_assoc_set (x: symbol_t, assoc: int): void
  = "atsyacc_symbol_assoc_set"

(* ****** ****** *)

fun symbol_term_total_get (): int
  = "atsyacc_symbol_term_total_get"

fun symbol_nonterm_total_get (): int

(* ****** ****** *)

abst@ype symbolset_t // a boxed type for sets of symbols

typedef symbolsetref = ref (symbolset_t)

fun symbolset_nil () : symbolsetref
  = "atsyacc_symbolset_nil"

fun symbolset_sing (x: symbol_t): symbolsetref
  = "atsyacc_symbolset_sing"

(*

fun symbolset_is_nil (xs: symbolsetref): bool
fun symbolset_isnot_nil (xs: symbolsetref): bool

*)

fun symbolset_ismem (xs: symbolsetref, x: symbol_t): bool
  = "atsyacc_symbolset_ismem"

fun symbolset_add (xs: symbolsetref, x: symbol_t): void
  = "atsyacc_symbolset_add"

fun symbolset_union (xs: symbolsetref, ys: symbolsetref): void
  = "atsyacc_symbolset_union"

fun symbolset_add_flag (xs: symbolsetref, x: symbol_t, flag: &int): void
  = "atsyacc_symbolset_add_flag"

fun symbolset_union_flag (xs: symbolsetref, ys: symbolsetref, flag: &int): void
  = "atsyacc_symbolset_union_flag"

//

fun fprint_symbolset {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, _: symbolsetref): void
  = "atsyacc_fprint_symbolset"

fun print_symbolset (_: symbolsetref): void
fun prerr_symbolset (_: symbolsetref): void

(* ****** ****** *)

fun symbol_nullable_get (x: symbol_t): bool
  = "atsyacc_symbol_nullable_get"
fun symbol_nullable_set (x: symbol_t, nullable: bool): void
  = "atsyacc_symbol_nullable_set"

fun symbol_frstset_get (x: symbol_t): symbolsetref
  = "atsyacc_symbol_frstset_get"
fun symbol_frstset_set (x: symbol_t, frstset: symbolsetref): void
  = "atsyacc_symbol_frstset_set"

fun symbol_fllwset_get (x: symbol_t): symbolsetref
  = "atsyacc_symbol_fllwset_get"
fun symbol_fllwset_set (x: symbol_t, fllwset: symbolsetref): void
  = "atsyacc_symbol_fllwset_set"

(* ****** ****** *)

(* end of [symbol.sats] *)
