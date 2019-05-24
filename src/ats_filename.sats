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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: July 2007
//
(* ****** ****** *)

staload Sym = "ats_symbol.sats"

(* ****** ****** *)

(* ats_filename: handling the names of files *)

(* ****** ****** *)

abstype filename_t // boxed type

(* ****** ****** *)

fun theDirsep_get
  (): char = "atsopt_filename_theDirsep_get"
fun theCurdir_get
  (): string = "atsopt_filename_theCurdir_get"
fun thePredir_get
  (): string = "atsopt_filename_thePredir_get"

(* ****** ****** *)

//

val filename_dummy : filename_t
val filename_stdin : filename_t

//

fun filename_isexi
  (name: string): bool = "atsopt_filename_isexi"
fun filename_is_relative (name: string): bool
fun filename_merge (fil: string, bas: string): string
  = "atsopt_filename_merge"
fun filename_append (dir: string, bas: string): string
  = "atsopt_filename_append"
//

fun filename_make_full (full: string): filename_t
fun filename_make_partfull (part: string, full: string): filename_t

//

fun filenameopt_make_relative (name: string): Option_vt (filename_t)

//

fun filename_part
  (f: filename_t): string
fun filename_full
  (f: filename_t): string = "atsopt_filename_full"
fun filename_full_sym (f: filename_t): $Sym.symbol_t

//

fun lt_filename_filename (f1: filename_t, f2: filename_t): bool
fun lte_filename_filename (f1: filename_t, f2: filename_t): bool
fun gt_filename_filename (f1: filename_t, f2: filename_t): bool
fun gte_filename_filename (f1: filename_t, f2: filename_t): bool

overload < with lt_filename_filename
overload <= with lte_filename_filename
overload > with gt_filename_filename
overload >= with gte_filename_filename

//

fun eq_filename_filename (f1: filename_t, f2: filename_t): bool
fun neq_filename_filename (f1: filename_t, f2: filename_t): bool

overload = with eq_filename_filename
overload <> with neq_filename_filename

//

fun compare_filename_filename (f1: filename_t, f2: filename_t): Sgn
overload compare with compare_filename_filename

(* ****** ****** *)

fun fprint_filename {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, f: filename_t): void

overload fprint with fprint_filename

fun print_filename (f: filename_t): void
fun prerr_filename (f: filename_t): void

overload print with print_filename
overload prerr with prerr_filename

(* ****** ****** *)

fun fprint_filename_base {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, f: filename_t): void
  = "atsopt_filename_fprint_filename_base"
// end of [fprint_filename_base]

fun print_filename_base (f: filename_t): void
fun prerr_filename_base (f: filename_t): void

(* ****** ****** *)

typedef path = string

fun path_normalize (s0: path): path

(* ****** ****** *)

fun the_pathlst_pop (): void
fun the_pathlst_push (p: path): void

(* ****** ****** *)

fun the_prepathlst_push (p: path): void

(* ****** ****** *)

fun the_filename_get (): filename_t
fun the_filenamelst_pop (): void
fun the_filenamelst_push (f: filename_t): void

//
// HX: (September 19, 2009)
// note that [ats_location.sats] staloads [ats_filename.sats];
// this solution is a bit unwieldy, but ...
//
abstype location_t // the same as the one in [ats_location.sats]
fun the_filenamelst_push_xit (loc0: location_t, f: filename_t): void

(* ****** ****** *)

fun atsopt_filename_prerr (): void = "atsopt_filename_prerr"
fun atsopt_filename_initialize (): void

(* ****** ****** *)

(* end of of [ats_filename.sats] *)
