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

(* static/dynamic environment *)

module DEXP2env : Ats_symenv.SymEnvType with type item = Ats_dynexp2.ditem2

val dexp2_env_add_con : Ats_staexp2.dcon2 -> unit
val dexp2_env_add_cst : Ats_dynexp2.dcst2 -> unit
val dexp2_env_add_mac : Ats_dynexp2.dmac2 -> unit
val dexp2_env_add_sym : Ats_symbol.symbol -> Ats_dynexp2.ditem2 -> unit
val dexp2_env_add_var : Ats_dynexp2.dvar2 -> unit
val dexp2_env_add_var_list : Ats_dynexp2.dvar2 list -> unit

val stadynenv2_pop : unit -> unit
val stadynenv2_push : unit -> unit
val stadynenv2_save : unit -> unit
val stadynenv2_restore : unit -> unit
val stadynenv2_localjoin : unit -> unit
val stadynenv2_pervasive : unit -> unit

val initialize : unit -> unit

(* end of [ats_stadynenv2.mli] *)
