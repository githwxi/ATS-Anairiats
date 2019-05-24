(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2012 Hongwei Xi, ATS Trustful Software, Inc.
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

abstype symbol_type // boxed
typedef symbol = symbol_type
typedef symbolist = List (symbol)
typedef symbolopt = Option (symbol)

(* ****** ****** *)

val symbol_empty : symbol

(* ****** ****** *)

fun eq_symbol_symbol (x1: symbol, x2: symbol):<> bool
overload = with eq_symbol_symbol
fun neq_symbol_symbol (x1: symbol, x2: symbol):<> bool
overload != with eq_symbol_symbol

fun compare_symbol_symbol (x1: symbol, x2: symbol):<> Sgn
overload compare with compare_symbol_symbol

(* ****** ****** *)

fun fprint_symbol
  (out: FILEref, x: symbol): void
overload fprint with fprint_symbol
fun print_symbol (x: symbol): void
overload print with print_symbol
fun prerr_symbol (x: symbol): void
overload prerr with prerr_symbol

(* ****** ****** *)

typedef stamp = uint

fun symbol_get_name (x: symbol):<> string
fun symbol_get_stamp (x: symbol):<> stamp
fun symbol_make_string (name: string): symbol

(* ****** ****** *)

(* end of [libatsdoc_symbol.sats] *)
