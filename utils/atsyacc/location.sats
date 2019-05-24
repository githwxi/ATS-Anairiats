(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
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
**
*)

(* ****** ****** *)

// Time: February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "libats/lex/lexing.sats"

(* ****** ****** *)

abstype location_t // boxed type

(* ****** ****** *)

val location_none : location_t (* nonexistent location *)

//

fun location_make
  (p1: position_t, p2: position_t):<> location_t
  = "atsyacc_location_make"

fun location_end_make (loc: location_t):<> location_t

fun location_combine (_1: location_t, _2: location_t):<> location_t

//

typedef lint = int_long_t0ype
fun location_begpos_toff (p: location_t): lint
fun location_endpos_toff (p: location_t): lint

//

fun lte_location_location (_1: location_t, _2: location_t):<> bool
overload <= with lte_location_location

//

fun fprint_location {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, loc: location_t): void

overload fprint with fprint_location

fun print_location (loc: location_t): void
fun prerr_location (loc: location_t): void

overload print with print_location
overload prerr with prerr_location

(* ****** ****** *)

(* end of [location.sats] *)
