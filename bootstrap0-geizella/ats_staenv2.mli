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

(* sort environment *)

module SRT2env: Ats_symenv.SymEnvType with type item = Ats_staexp2.srtext2

(* static expression environment *)

module SEXP2env: Ats_symenv.SymEnvType with type item = Ats_staexp2.sitem2

val srt2_env_add_var : Ats_staexp2.srt2_var -> unit

val srt2_env_add_var_list : Ats_staexp2.srt2_var list -> unit

val sexp2_env_add_cst_list : Ats_syntax.sid -> Ats_staexp2.scst2 list -> unit

val sexp2_env_add_datcon : Ats_staexp2.dcon2 -> unit

val sexp2_env_add_fil : Ats_syntax.sid -> Ats_filename.filename -> unit

val sexp2_env_add_mod :
  Ats_syntax.sid -> Ats_staexp2.labsvar2 list -> Ats_staexp2.sexp2 -> unit

val sexp2_env_add_var : Ats_staexp2.svar2 -> unit

val sexp2_env_add_var_list : Ats_staexp2.svar2 list -> unit

(* ****** ****** *)

(* end of [ats_staenv2.mli] *)
