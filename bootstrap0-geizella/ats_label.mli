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

(* ats_label: handling labels *)

(* ****** ****** *)

type label

type intinf = Big_int.big_int
type symbol = Ats_symbol.symbol

val make_with_int : int -> label
val make_with_intinf : intinf -> label
val make_with_string : string -> label
val make_with_symbol : symbol -> label

val compare : label -> label -> int

val eq : label -> label -> bool
val neq : label -> label -> bool
val lt : label -> label -> bool
val lte : label -> label -> bool
val gt : label -> label -> bool
val gte : label -> label -> bool

val fprint : out_channel -> label -> unit
val fprint_list : out_channel -> label list -> unit
val fprint_opt : out_channel -> label option -> unit

val prerr : label -> unit
val print : label -> unit

val labeled_list_find : (label * 'a) list -> label -> 'a option
val labeled_list_sort : (label * 'a) list -> (label * 'a) list

val int_of : label -> int option
val sym_of : label -> symbol option

val string_of : label -> string

val is_prefix : label list -> label list -> (label list) option

(* ****** ****** *)

(* end of [ats_label.mli] *)
