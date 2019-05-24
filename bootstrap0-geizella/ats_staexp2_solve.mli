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
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
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

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

type loc = Ats_location.location

val clokind_equal_solve : loc -> int -> int -> unit

val funclo_equal_solve :
  loc -> Ats_syntax.funclo -> Ats_syntax.funclo -> unit

val funlinear_equal_solve : loc -> int -> int -> unit

val pfarity_equal_solve : loc -> int -> int -> unit

val sexp2_equal_solve : loc -> Ats_staexp2.sexp2 -> Ats_staexp2.sexp2 -> unit
val sexp2_list_equal_solve : loc ->
  Ats_staexp2.sexp2 list -> Ats_staexp2.sexp2 list -> unit
val sexp2_list_list_equal_solve : loc ->
  Ats_staexp2.sexp2 list list -> Ats_staexp2.sexp2 list list -> unit
val labsexp2_list_equal_solve : loc ->
  Ats_staexp2.labsexp2 list -> Ats_staexp2.labsexp2 list -> unit
val sexp2_szleq_solve : loc -> Ats_staexp2.sexp2 -> Ats_staexp2.sexp2 -> unit
val sexp2_szeqeq_solve : loc -> Ats_staexp2.sexp2 -> Ats_staexp2.sexp2 -> unit
val sexp2_void_solve : loc -> Ats_staexp2.sexp2 -> unit

(* ****** ****** *)

val sexp2_tyleq_solve : loc -> Ats_staexp2.sexp2 -> Ats_staexp2.sexp2 -> unit
val sexp2_list_tyleq_solve : loc ->
  Ats_staexp2.sexp2 list -> Ats_staexp2.sexp2 list -> unit
val labsexp2_list_tyleq_solve : loc ->
  Ats_staexp2.labsexp2 list -> Ats_staexp2.labsexp2 list -> unit
val labsexp2_list_tyrec_tyleq_solve : loc ->
  Ats_staexp2.tyrec_kind -> int (* arity_p *) ->
  Ats_staexp2.labsexp2 list -> Ats_staexp2.sexp2 -> unit
val sexp2_list_tyleq_solve_with_vars : loc ->
  Ats_staexp2.sexp2 list -> Ats_staexp2.sexp2 list ->
  (Ats_syntax.sid option * Ats_staexp2.srt2 * int) list -> unit

val sexp2_eff_leq_solve : loc -> Ats_staexp2.seff2 -> Ats_staexp2.seff2 -> unit

(* ****** ****** *)

val sexp2_tyleq_solve_Var_l : loc -> Ats_staexp2.sVar2 -> Ats_staexp2.sexp2 -> unit
val sexp2_tyleq_solve_Var_r :
  loc -> Ats_staexp2.sexp2 -> Ats_staexp2.sVar2 -> Ats_staexp2.sexp2 -> unit

(* ****** ****** *)

val sexp2_equal_solve_Var : loc ->
  Ats_staexp2.sVar2 -> Ats_staexp2.sexp2 -> Ats_staexp2.sexp2 -> unit
val sexp2_tyleq_solve_VarApp : loc -> bool ->
  Ats_staexp2.sVar2 -> Ats_staexp2.sexp2 -> Ats_staexp2.sexp2 -> unit

(* ****** ****** *)

val sexp2_hyeq_solve : loc -> Ats_staexp2.sexp2 -> Ats_staexp2.sexp2 -> unit
val sexp2_list_hyeq_solve : loc ->
  Ats_staexp2.sexp2 list -> Ats_staexp2.sexp2 list -> unit

(* ****** ****** *)

(* end of [ats_staexp2_solve.mli] *)
