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

(* Mainly for checking pattern mattching exhaustiveness *)

type intinf = Big_int.big_int

type loc = Ats_location.location
type lab = Ats_label.label

type dcon2 = Ats_staexp2.dcon2
type pat2 = Ats_dynexp2.pat2

type patcst2 =
  | PTC2any
  | PTC2bool of bool (* boolean pattern *)
  | PTC2char of char (* character pattern *)
  | PTC2con of dcon2 * patcst2 list (* constructor pattern *)
  | PTC2empty
  | PTC2int of intinf (* integer pattern *)
  | PTC2intc of intinf list (* complement integer pattern *)
  | PTC2rec of labpatcst2 list (* record pattern *)
  | PTC2string of string
  | PTC2vbox (* vbox pattern *)

and labpatcst2 = lab * patcst2

val fprint_patcst2 : out_channel -> patcst2 -> unit
val fprint_patcst2_list : out_channel -> patcst2 list -> unit
val fprint_patcst2_list_list : out_channel -> patcst2 list list -> unit

val fprint_labpatcst2 : out_channel -> labpatcst2 -> unit
val fprint_labpatcst2_list : out_channel -> labpatcst2 list -> unit

val patcst2_of_pat2 : pat2 -> patcst2
val patcst2_of_pat2_list : pat2 list -> patcst2 list

val patcst2_is_ints  : patcst2 -> patcst2 -> bool
val patcst2_list_is_ints  : patcst2 list -> patcst2 list -> bool

val patcst2_comp : patcst2 -> patcst2 list
val patcst2_list_comp : patcst2 list -> (patcst2 list) list

val patcst2_diff : patcst2 -> patcst2 -> patcst2 list
val patcst2_list_diff : patcst2 list -> patcst2 list -> patcst2 list list

val cla2_pat_comp : Ats_dynexp2.cla2 -> patcst2 list list

(* ****** ****** *)

(* end of [ats_patcst2.mli *)
