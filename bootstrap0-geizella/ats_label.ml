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

open Ats_misc

module BI = Big_int
module Sym = Ats_symbol

(* ****** ****** *)

type intinf = BI.big_int
type symbol = Sym.symbol

(* ****** ****** *)

type label = LABint of int | LABsym of symbol

let make_with_int i = LABint i
let make_with_intinf i = LABint (BI.int_of_big_int i)
let make_with_string s = LABsym (Sym.make_with_string s)
let make_with_symbol s = LABsym s

let compare l1 l2 = match (l1, l2) with
  | (LABsym s1, LABsym s2) -> Sym.compare s1 s2
  | (LABint i1, LABint i2) -> compare i1 i2
  | (LABsym _, LABint _) -> 1
  | (LABint _, LABsym _) -> -1

let eq l1 l2 = compare l1 l2 == 0
let neq l1 l2 = compare l1 l2 <> 0

let lt l1 l2 = compare l1 l2 == -1
let lte l1 l2 = compare l1 l2 <> 1
let gt l1 l2 = compare l1 l2 == 1
let gte l1 l2 = compare l1 l2 <> -1

(* ****** ****** *)

let fprint out l = match l with
  | LABsym s -> Sym.fprint out s
  | LABint i -> fprint_int out i

let fprint_list out ls = fprint_list_with_sep fprint out ls ","

let fprint_opt out ol =
  match ol with None -> () | Some l -> fprint out l

let print l = fprint stdout l
let prerr l = fprint stderr l

(* ****** ****** *)

let labeled_list_find lxs l0 =
  let rec aux = function
    | (l, x) :: lxs -> if eq l0 l then Some x else aux lxs
    | [] -> None in
    aux lxs

let labeled_list_sort lxs =
  List.sort (fun (l1, _) (l2, _) -> compare l1 l2) lxs

(* ****** ****** *)

let int_of l = match l with
  | LABint i -> Some i
  | LABsym _ -> None

let sym_of l = match l with
  | LABint _ -> None
  | LABsym s -> Some s

let string_of l = match l with
  | LABint i -> string_of_int i
  | LABsym s -> Sym.string_of s

(* ****** ****** *)

let is_prefix ls1 ls2 =
  let rec aux ls1 ls2 = match ls1, ls2 with
    | [], _ -> Some ls2
    | _, [] -> None
    | l1 :: ls1, l2 :: ls2 ->
	if eq l1 l2 then aux ls1 ls2 else None in
    aux ls1 ls2
(* end of [is_prefix] *)

(* ****** ****** *)

(* end of [ats_label.ml] *)
