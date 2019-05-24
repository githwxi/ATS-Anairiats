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

(* ats_counter: implementing counters *)

(* ****** ****** *)

type count
type counter

val zero : count

val eq : count -> count -> bool
val neq : count -> count -> bool
val compare : count -> count -> int

module CountMap : Map.S with type key = count

(* ****** ****** *)

val fprint : out_channel -> count -> unit
val string_of : count -> string

val make_counter : unit -> counter

val srt2_dat_new_stamp : unit -> count
val scst2_new_stamp : unit -> count
val struct2_new_stamp : unit -> count

val svar2_new_stamp : unit -> count
val svar2_new_name : unit -> Ats_symbol.symbol
val svar2_new_name_with_prefix : string -> Ats_symbol.symbol

val sVar2_new_stamp : unit -> count
val sVar2_new_name : unit -> count

val dcon2_new_stamp : unit -> count
val dcst2_new_stamp : unit -> count
val dmac2_new_stamp : unit -> count
val dvar2_new_stamp : unit -> count
val dvar2_new_name : unit -> Ats_symbol.symbol

val funlab_new_stamp : unit -> count
val tmplab_new_stamp : unit -> count
val tmpvar_new_stamp : unit -> count

(* ****** ****** *)

val initialize : unit -> unit

(* ****** ****** *)

(* end of [ats_counter.mli] *)
