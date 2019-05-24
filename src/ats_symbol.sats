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
// Time: August 2007

(* ****** ****** *)

(* ats_symbol: implementing symbol table facilities for ATS *)

(* ****** ****** *)

abstype symbol_t // boxed type: implemented in [ats_symbol.dats]

(* ****** ****** *)

val symbol_empty : symbol_t

(* various symbols *)

val symbol_ADD : symbol_t
val symbol_AMPERSAND : symbol_t
val symbol_AT : symbol_t
val symbol_BACKSLASH : symbol_t
val symbol_BANG : symbol_t
val symbol_COLONEQ : symbol_t
val symbol_DIV : symbol_t
val symbol_EQ : symbol_t
val symbol_EQEQ : symbol_t
val symbol_FUN: symbol_t
val symbol_GT : symbol_t
val symbol_GTEQ : symbol_t
val symbol_GTGT : symbol_t
val symbol_GTLT : symbol_t
val symbol_LAND : symbol_t
val symbol_LOR : symbol_t
val symbol_LRBRACKETS : symbol_t
val symbol_LT : symbol_t
val symbol_LTEQ : symbol_t
val symbol_LTLT : symbol_t
val symbol_MINUSGT : symbol_t
val symbol_MINUSLTGT : symbol_t
val symbol_MUL : symbol_t
val symbol_NEQ : symbol_t
val symbol_NEQEQ : symbol_t
val symbol_QMARK : symbol_t
val symbol_QMARKBANG : symbol_t
val symbol_SUB : symbol_t
val symbol_TILDE : symbol_t
val symbol_UNDERSCORE : symbol_t
//
val symbol_FALSE : symbol_t
val symbol_TRUE : symbol_t
//
val symbol_DO : symbol_t
val symbol_FOR : symbol_t
val symbol_IF : symbol_t
val symbol_IN : symbol_t
val symbol_R0EAD : symbol_t // r@ead: read-only annotation
val symbol_SIZEOF : symbol_t
val symbol_STDIN : symbol_t
val symbol_TUPZ : symbol_t // TUPIZE
val symbol_UNION : symbol_t
val symbol_VBOX : symbol_t
val symbol_WHILE : symbol_t

(* macro expansion *)

val symbol_DEFINED : symbol_t
val symbol_UNDEFINED : symbol_t

val symbol_EVALMAC : symbol_t
val symbol_LIFTMAC : symbol_t

val symbol_IS_NIL : symbol_t
val symbol_IS_CONS : symbol_t
val symbol_TUP_HEAD : symbol_t
val symbol_TUP_TAIL : symbol_t

(* base sorts *)

val symbol_ADDR : symbol_t
val symbol_BOOL : symbol_t
val symbol_CHAR : symbol_t
val symbol_CLS : symbol_t
val symbol_EFF : symbol_t
val symbol_EXN : symbol_t
val symbol_INT : symbol_t

(* base impredicative sorts *)

val symbol_PROP : symbol_t
val symbol_TYPE : symbol_t // types of one word size
val symbol_T0YPE : symbol_t // types of unspecified size
val symbol_VIEW : symbol_t
val symbol_VIEWTYPE : symbol_t // viewtypes of one word size
val symbol_VIEWT0YPE : symbol_t // viewtypes of unspecified size
val symbol_TYPES : symbol_t // type lists

(* ****** ****** *)

(*
//
// special variables for object-oriented programming
//
val symbol_SELF : symbol_t
val symbol_MYCLS : symbol_t
*)

(* ****** ****** *)
//
// the prefix for function name generation
//
val symbol_ATSOPT_NAMESPACE : symbol_t

//
// static loading at run-time is needed or not
//
val symbol_ATS_STALOADFLAG : symbol_t

//
// dynamic loading at run-time is needed or not
//
val symbol_ATS_DYNLOADFLAG : symbol_t

//
// the name of the dynamic loading function
//
val symbol_ATS_DYNLOADFUN_NAME : symbol_t

(* ****** ****** *)

fun symbol_name (symbol: symbol_t):<> string
fun symbol_make_string (name: string): symbol_t

(* ****** ****** *)

fun lt_symbol_symbol (s1: symbol_t, s2: symbol_t):<> bool
overload < with lt_symbol_symbol

fun lte_symbol_symbol (s1: symbol_t, s2: symbol_t):<> bool
overload <= with lte_symbol_symbol

fun gt_symbol_symbol (s1: symbol_t, s2: symbol_t):<> bool
overload > with gt_symbol_symbol

fun gte_symbol_symbol (s1: symbol_t, s2: symbol_t):<> bool
overload >= with gte_symbol_symbol

fun eq_symbol_symbol (s1: symbol_t, s2: symbol_t):<> bool
overload = with eq_symbol_symbol

fun neq_symbol_symbol (s1: symbol_t, s2: symbol_t):<> bool
overload <> with neq_symbol_symbol

fun compare_symbol_symbol (s1: symbol_t, s2: symbol_t):<> Sgn
overload compare with compare_symbol_symbol

(* ****** ****** *)

fun symbol_hash (s: symbol_t):<> uInt

(* ****** ****** *)

fun fprint_symbol {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s: symbol_t): void
overload fprint with fprint_symbol

fun print_symbol (s: symbol_t): void
overload print with print_symbol

fun prerr_symbol (s: symbol_t): void
overload prerr with prerr_symbol

(* ****** ****** *)

fun fprint_symbol_code {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s: symbol_t): void
// end of [fprint_symbol_code]

fun print_symbol_code (s: symbol_t): void
fun prerr_symbol_code (s: symbol_t): void

(* ****** ****** *)

(* end of [ats_symbol.sats] *)
