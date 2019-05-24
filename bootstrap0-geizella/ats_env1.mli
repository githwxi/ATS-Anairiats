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

val fixity_add_opr : Ats_syntax.id -> Ats_fixity.fixity -> unit
val fixity_find_opr : Ats_syntax.id -> Ats_fixity.fixity option
val fixity_find_srt_opr : Ats_syntax.srt_id -> Ats_fixity.fixity option
val fixity_find_sexp_opr : Ats_syntax.sid -> Ats_fixity.fixity option
val fixity_find_dexp_opr : Ats_syntax.did -> Ats_fixity.fixity option

(* ****** ******* *)

module E0xpEnv : Ats_symenv.SymEnvType
val e0xp1_add_id : Ats_syntax.id -> Ats_staexp1.e0xp1 -> unit
val e0xp1_find_sym : Ats_symbol.symbol -> Ats_staexp1.e0xp1 option
val e0xp1_find_id : Ats_syntax.id -> Ats_staexp1.e0xp1 option

(* ****** ******* *)

val env_pop : unit -> unit
val env_push : unit  -> unit

val env_save : unit -> unit
val env_restore : unit  -> unit

(* <env_localjoin> is for handling <local ... in ... end> *)
val env_localjoin : unit -> unit

(* make the top environment pervasive *)
val env_make_top_pervasive : unit -> unit

(* end of [ats_env1.mli] *)
