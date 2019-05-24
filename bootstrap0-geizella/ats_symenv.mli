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

(* ats_symenv: implementing symbol enviroments *)

(* ****** ****** *)

type symbol = Ats_symbol.symbol

module type SymEnvType = sig
  type item (* transparent *)
  type table (* opque *)

  val add: symbol -> item -> unit
  val add_list: (symbol * item) list -> unit
  val empty: table
  val find: symbol -> item option
  val find_in_pervasives: symbol -> item option
  val get_top: unit -> table
  val initialize: unit -> unit
  val localjoin: unit -> unit (* for handling <local ... in ... end> *)
  val make_pervasive: table -> unit
  val make_top_pervasive: unit -> unit
  val pop: unit -> unit
  val push: unit -> unit
  val restore: unit -> unit
  val save: unit -> unit
  val set_top: table -> unit
  val table_find: symbol -> table -> item option
  val top_to_list: unit -> item list
  val all_to_list: unit -> item list
end (* end of EnvType *)

module SymEnvFun (X: sig type item end)
  : SymEnvType with type item = X.item

(* ****** ****** *)

(* end of [ats_symenv.mli] *)
