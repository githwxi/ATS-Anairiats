(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
*)

(* ****** ****** *)

(* author: Rick Lavoie (coldfury AT cs DOT bu DOT edu) *)
(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [printf.sats] starts!\n"
#endif // end of [VERBOSE_PRELUDE]

(* ****** ****** *)

fun fprintf_err {m:file_mode} {ts:types} (
    pf: file_mode_lte (m, w)
  | out: &FILE m
  , fmt: printf_c ts
  , arg: ts
  ) :<!ref> int
  = "atspre_fprintf_err"

symintr fprintf

fun fprintf0_exn {ts:types}
  (out: FILEref, fmt: printf_c ts, arg: ts):<!exnref> void
  = "atspre_fprintf_exn"

fun fprintf1_exn {m:file_mode} {ts:types} (
    pf: file_mode_lte (m, w)
  | out: &FILE m
  , fmt: printf_c ts
  , arg: ts
  ) :<!exnref> void
  = "atspre_fprintf_exn"

overload fprintf with fprintf0_exn
overload fprintf with fprintf1_exn

(* ****** ****** *)

fun printf_err {ts:types}
  (fmt: printf_c ts, arg: ts):<!ref> int = "atspre_printf_err"
// end of [printf_err]

fun printf {ts:types}
  (fmt: printf_c ts, arg: ts):<!exnref> void = "atspre_printf_exn"
// end of [printf_exn]

fun prerrf {ts:types}
  (fmt: printf_c ts, arg: ts):<!exnref> void = "atspre_prerrf_exn"
// end of [prerrf_exn]

(* ****** ****** *)

symintr assert_prerrf
 
fun assert_prerrf_bool {ts:types}
  (assertion: bool, fmt: printf_c ts, arg: ts):<!exn> void
  = "atspre_assert_prerrf"

fun assert_prerrf_bool1 {b:bool} {ts:types}
  (assertion: bool b, fmt: printf_c ts, arg: ts):<!exn> [b] void
  = "atspre_assert_prerrf"

overload assert_prerrf with assert_prerrf_bool
overload assert_prerrf with assert_prerrf_bool1

(* ****** ****** *)

fun tostringf_size {ts:types}
  (guess: Nat, fmt: printf_c ts, arg: ts):<> String
  = "atspre_tostringf_size"

fun tostringf {ts:types}
  (fmt: printf_c ts, arg: ts):<> strptr1 = "atspre_tostringf"

fun sprintf {ts:types}
  (fmt: printf_c ts, arg: ts):<> strptr1 = "atspre_tostringf"

(* ****** ****** *)

(* [fprintf_ats] is to be implemented as a macro if there is a need. *)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [printf.sats] finishes!\n"
#endif // end of [VERBOSE_PRELUDE]

(* end of [printf.sats] *)
