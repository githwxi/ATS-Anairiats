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

open Ats_misc
open Ats_staexp2
open Ats_staexp2_util
open Ats_dynexp2
open Ats_dyncst2

module BI = Big_int
module PR = Printf

module Err = Ats_error
module Lab = Ats_label
module Loc = Ats_location

(* ****** ****** *)

type intinf = BI.big_int

type loc = Loc.location
type lab = Lab.label

type dcon2 = Ats_staexp2.dcon2
type pat2 = Ats_dynexp2.pat2

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_pat2_comp: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

(* constant patterns *)

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
(* end of [patcst2] *)

and labpatcst2 = lab * patcst2

let fprint_intinf_list (out: out_channel) (xs: intinf list) =
  fprint_list_with_sep fprint_intinf out xs ","

let rec fprint_patcst2 (out: out_channel) (p2tc: patcst2): unit =
  match p2tc with
  | PTC2any -> PR.fprintf out "PTC2any"
  | PTC2bool b -> PR.fprintf out "PTC2bool(%b)" b
  | PTC2char c -> PR.fprintf out "PTC2char(%c)" c
  | PTC2con (d2c, p2tcs) ->
      PR.fprintf out "PTC2con(%a; %a)" fprint_dcon2 d2c fprint_patcst2_list p2tcs
  | PTC2empty -> PR.fprintf out "PTC2empty()"
  | PTC2int x -> PR.fprintf out "PTC2int(%s)" (string_of_intinf x)
  | PTC2intc xs -> PR.fprintf out "PTC2intc(%a)" fprint_intinf_list xs
  | PTC2rec lp2tcs -> PR.fprintf out "PTC2rec(%a)" fprint_labpatcst2_list lp2tcs
  | PTC2string s -> PR.fprintf out "PTC2string(%s)" s
  | PTC2vbox -> PR.fprintf out "PTC2vbox"
(* end of [fprint_patcst2] *)

and fprint_patcst2_list
  (out: out_channel) (p2tcs: patcst2 list): unit =
  fprint_list_with_sep fprint_patcst2 out p2tcs ","

and fprint_patcst2_list_list
  (out: out_channel) (p2tcss: patcst2 list list): unit =
  fprint_list_with_sep fprint_patcst2_list out p2tcss ","

and fprint_labpatcst2
  (out: out_channel) ((l, p2tc): labpatcst2): unit =
  PR.fprintf out "%a=%a" Lab.fprint l fprint_patcst2 p2tc

and fprint_labpatcst2_list
  (out: out_channel) (lp2tcs: labpatcst2 list): unit =
  fprint_list_with_sep fprint_labpatcst2 out lp2tcs ","

(* ****** ****** *)

let rec pat2_is_cmplt (p2t: pat2): bool =
  match p2t.pat2_node with
    | PT2ann (p2t, _) -> pat2_is_cmplt p2t
    | PT2any -> true
    | PT2char c -> false
    | PT2con (is_ref, d2c, _, _, _, (npf, p2ts)) ->
	scst2_is_singular d2c.dcon2_scst && pat2_list_is_cmplt p2ts
    | PT2empty -> true
    | PT2exi (_, p2t) -> pat2_is_cmplt p2t
    | PT2int i -> false
    | PT2rec (is_flat, is_omit, (npf, lp2ts)) -> labpat2_list_is_cmplt lp2ts
    | PT2string s -> false
    | PT2var (_, _, op2t) -> begin match op2t with
	| Some p2t -> pat2_is_cmplt p2t | None -> true
      end
    | _ -> error_of_unavailability "ats_pat2_complemet: pat2_is_cmplt"
(* end of [pat2_is_cmplt] *)

and pat2_list_is_cmplt (p2ts: pat2 list): bool =
  List.for_all pat2_is_cmplt p2ts

and labpat2_list_is_cmplt (lp2ts: labpat2 list): bool =
  List.for_all (function (l, p2t) -> pat2_is_cmplt p2t) lp2ts

(* ****** ****** *)

let rec patcst2_is_cmplt (p2tc: patcst2): bool =
  match p2tc with
    | PTC2any -> true
    | PTC2bool b -> false
    | PTC2char c -> false
    | PTC2con (d2c, p2tcs) ->
	scst2_is_singular d2c.dcon2_scst && patcst2_list_is_cmplt p2tcs
    | PTC2empty -> true
    | PTC2int i -> false
    | PTC2intc xs -> list_is_empty xs
    | PTC2rec lp2tcs -> labpatcst2_list_is_cmplt lp2tcs
    | PTC2string s -> false
    | PTC2vbox -> true
(* end of [patcst2_is_cmplt] *)

and patcst2_list_is_cmplt (p2tcs: patcst2 list): bool =
  List.for_all patcst2_is_cmplt p2tcs

and labpatcst2_list_is_cmplt (lp2tcs: labpatcst2 list): bool =
  List.for_all (function (l, p2tc) -> patcst2_is_cmplt p2tc) lp2tcs

(* ****** ****** *)

let patcst2_lst (p2tcs: patcst2 list): patcst2 =
  let d2c_nil = dcon2_list_nil () in
  let d2c_cons = dcon2_list_cons () in
  let rec aux p2tcs = match p2tcs with
    | [] -> PTC2con (d2c_nil, [])
    | p2tc :: p2tcs -> PTC2con (d2c_cons, [p2tc; aux p2tcs]) in
    aux p2tcs
(* end of [patcst2_lst] *)

let rec patcst2_of_pat2 (p2t: pat2): patcst2 =
  match p2t.pat2_node with
    | PT2ann (p2t, _) -> patcst2_of_pat2 p2t
    | PT2any -> PTC2any
    | PT2bool b -> PTC2bool b
    | PT2char c -> PTC2char c
    | PT2con (is_ref, d2c, _, _, _, (npf, p2ts)) ->
	PTC2con (d2c, patcst2_of_pat2_list p2ts)
    | PT2empty -> PTC2empty
    | PT2exi (_, p2t) -> patcst2_of_pat2 p2t
    | PT2int i -> PTC2int i
    | PT2lst p2ts -> patcst2_lst (patcst2_of_pat2_list p2ts)
    | PT2rec (is_flat, is_omit, (npf, lp2ts)) ->
	PTC2rec (labpatcst2_of_labpat2_list lp2ts)
    | PT2string s -> PTC2string s
    | PT2var (_, _, op2t) -> begin match op2t with
	| Some p2t -> patcst2_of_pat2 p2t | None -> PTC2any
      end
    | PT2vbox _ -> PTC2vbox
    | _ -> begin
	PR.fprintf stderr "patcst2_of_pat2: %a\n" fprint_pat2 p2t;
	Err.abort ();
      end
(* end of [patcst2_of_pat2] *)

and patcst2_of_pat2_list (p2ts: pat2 list): patcst2 list =
  List.map patcst2_of_pat2 p2ts

and labpatcst2_of_labpat2_list (lp2ts: labpat2 list): labpatcst2 list =
  List.map (function (l, p2t) -> (l, patcst2_of_pat2 p2t)) lp2ts

(* ****** ****** *)

(* [p2tc1] matches more than [p2tc2] *)

let rec patcst2_is_sup (p2tc1: patcst2) (p2tc2: patcst2): bool =
  match p2tc1, p2tc2 with
    | PTC2any, _ -> true
    | PTC2bool b1, PTC2bool b2 -> b1 = b2
    | PTC2char c1, PTC2char c2 -> c1 = c2
    | PTC2con (d2c1, p2tcs1), PTC2con (d2c2, p2tcs2) ->
	dcon2_eq d2c1 d2c2 && patcst2_list_is_sup p2tcs1 p2tcs2
    | PTC2empty, PTC2empty -> true
    | PTC2int i1, PTC2int i2 -> i1 = i2
    | PTC2intc xs, PTC2int i -> List.for_all (function x -> intinf_neq x i) xs
    | PTC2rec lp2tcs1, PTC2rec lp2tcs2 -> labpatcst2_list_is_sup lp2tcs1 lp2tcs2
    | PTC2vbox, PTC2vbox -> true
    | _, _ -> false
(* end of [patcst2_is_sup] *)

and patcst2_list_is_sup (p2tcs1: patcst2 list) (p2tcs2: patcst2 list): bool =
  match p2tcs1, p2tcs2 with
    | [], _ -> true
    | _, [] -> false
    | p2tc1 :: p2tcs1, p2tc2 :: p2tcs2 ->
	patcst2_is_sup p2tc1 p2tc2 && patcst2_list_is_sup p2tcs1 p2tcs2
(* end of [patcst2_list_is_sup] *)

and labpatcst2_list_is_sup
  (lp2tcs1: labpatcst2 list) (lp2tcs2: labpatcst2 list): bool =
  match lp2tcs1, lp2tcs2 with
    | [], _ -> true
    | _, [] -> labpatcst2_list_is_cmplt lp2tcs1
    | (l1, p2tc1) :: lp2tcs1', (l2, p2tc2) :: lp2tcs2' ->
	if Lab.eq l1 l2 then
	  (patcst2_is_sup p2tc1 p2tc2 && labpatcst2_list_is_sup lp2tcs1' lp2tcs2')
	else
	  (patcst2_is_cmplt p2tc1 && labpatcst2_list_is_sup lp2tcs1' lp2tcs2)
(* end of [labpatcst2_list_is_sup] *)

(* ****** ****** *)

(* [p2tc1] intersects [p2tc2] *)

let rec patcst2_is_ints (p2tc1: patcst2) (p2tc2: patcst2): bool =
  match p2tc1, p2tc2 with
    | PTC2any, _ -> true
    | _, PTC2any -> true
    | PTC2bool b1, PTC2bool b2 -> b1 = b2
    | PTC2char c1, PTC2char c2 -> c1 = c2
    | PTC2con (d2c1, p2tcs1), PTC2con (d2c2, p2tcs2) ->
	dcon2_eq d2c1 d2c2 && patcst2_list_is_ints p2tcs1 p2tcs2
    | PTC2empty, PTC2empty -> true
    | PTC2int i1, PTC2int i2 -> i1 = i2
    | PTC2int i, PTC2intc xs -> List.for_all (function x -> intinf_neq i x) xs
    | PTC2intc xs, PTC2int i -> List.for_all (function x -> intinf_neq x i) xs
    | PTC2intc _, PTC2intc _ -> true
    | PTC2vbox, PTC2vbox -> true
    | _, _ -> false
(* end of [patcst2_is_ints] *)

and patcst2_list_is_ints (p2tcs1: patcst2 list) (p2tcs2: patcst2 list): bool =
(*
  let () =
    PR.fprintf stdout
      "patcst2_list_is_ints: p2tcs1 = %a\n" fprint_patcst2_list p2tcs1 in
  let () =
    PR.fprintf stdout
      "patcst2_list_is_ints: p2tcs2 = %a\n" fprint_patcst2_list p2tcs2 in
*)
  List.for_all2 patcst2_is_ints p2tcs1 p2tcs2

(* ****** ****** *)

(* computing the complement of a constant pattern *)
let rec patcst2_comp (p2tc: patcst2): patcst2 list =
  match p2tc with
    | PTC2any -> []
    | PTC2bool b -> if b then [PTC2bool false] else [PTC2bool true]
    | PTC2char _ -> [PTC2any] (* a crude approximation *)
    | PTC2con (d2c, p2tcs) -> begin
	let d2cs =
	  let s2c = d2c.dcon2_scst in match s2c.scst2_cons with
	    | Some d2cs -> d2cs
	    | None -> error_of_deadcode "ats_pat2_comp: pat2_comp" in
	  patcst2_con_comp d2c d2cs p2tcs
      end
    | PTC2empty -> []
    | PTC2int x -> [PTC2intc [x]]
    | PTC2intc xs -> List.map (function x -> PTC2int x) xs
    | PTC2rec lp2tcs ->
	List.map (function lp2tcs -> PTC2rec lp2tcs) (labpatcst2_list_comp lp2tcs)
    | PTC2string _ -> [PTC2any] (* a crude approximation *)
    | PTC2vbox -> []
(* end of [patcst2_comp] *)

and patcst2_con_comp
  (d2c0: dcon2) (d2cs: dcon2 list) (p2tcs: patcst2 list): patcst2 list =
  let rec aux (res: patcst2 list) = function
    | d2c :: d2cs -> begin
	if dcon2_eq d2c0 d2c then
	  let p2tcss = patcst2_list_comp p2tcs in
	  let res =
	    List.fold_left
	      (fun res p2tcs -> PTC2con (d2c, p2tcs) :: res) res p2tcss in
	    aux res d2cs
	else
	  let p2tc =
	    let (npf, s2es) = d2c.dcon2_arg in
	    let p2tcs = List.map (function _ -> PTC2any) s2es in
	      PTC2con (d2c, p2tcs) in
	    aux (p2tc :: res) d2cs
      end
    | [] -> List.rev res in
    aux [] d2cs
(* end of [patcst2_con_comp] *)

and patcst2_list_comp (p2tcs: patcst2 list): (patcst2 list) list =
  match p2tcs with
    | p2tc :: p2tcs ->
	let p2tcss1 =
	  let p2tcs = List.map (function _ -> PTC2any) p2tcs in
	    List.map (function p2tc -> p2tc :: p2tcs) (patcst2_comp p2tc) in
	let p2tcss2 = 
	  let p2tc = PTC2any in
	    List.map (function p2tcs -> p2tc :: p2tcs) (patcst2_list_comp p2tcs) in
	  p2tcss1 @ p2tcss2
    | [] -> []
(* end of [patcst2_list_comp] *)

and labpatcst2_list_comp (lp2tcs: labpatcst2 list): (labpatcst2 list) list =
  match lp2tcs with
    | (l, p2tc) :: lp2tcs ->
	let lp2tcss1 =
	  let lp2tcs = List.map (function (l, _) -> (l, PTC2any)) lp2tcs in
	    List.map (function p2tc -> (l, p2tc) :: lp2tcs) (patcst2_comp p2tc) in
	let lp2tcss2 = 
	  let p2tc = PTC2any in
	    List.map
	      (function lp2tcs -> (l, p2tc) :: lp2tcs) (labpatcst2_list_comp lp2tcs) in
	  lp2tcss1 @ lp2tcss2
    | [] -> []
(* end of [labpatcst2_list_comp] *)

(* ****** ****** *)

let rec patcst2_diff (p2tc1: patcst2) (p2tc2: patcst2): patcst2 list =
  match p2tc1, p2tc2 with
    | _, PTC2any -> []
    | PTC2any, _ -> patcst2_comp p2tc2
    | PTC2bool b1, PTC2bool b2 -> if b1 = b2 then [] else [p2tc1]
    | PTC2char c1, PTC2char c2 -> if c1 = c2 then [] else [p2tc1]
    | PTC2con (d2c1, p2tcs1), PTC2con (d2c2, p2tcs2) ->
	if dcon2_eq d2c1 d2c2 then
	  let p2tcss = patcst2_list_diff p2tcs1 p2tcs2 in
	    List.map (function p2tcs -> PTC2con (d2c1, p2tcs)) p2tcss
	else [p2tc1]
    | PTC2empty, PTC2empty -> []
    | PTC2intc xs, PTC2int i ->
	if List.exists (function x -> intinf_eq x i) xs then [p2tc1]
	else [PTC2intc (i :: xs)]
    | PTC2vbox, PTC2vbox -> []
    | _, _ -> error "patcst2diff: yet to be done"
(* end of [patcst2_diff] *)

and patcst2_list_diff
  (p2tcs1: patcst2 list) (p2tcs2: patcst2 list): patcst2 list list =
  match p2tcs1, p2tcs2 with
    | [], [] -> []
    | p2tc1 :: p2tcs1, p2tc2 :: p2tcs2 -> begin
	let p2tcss1 =
	  List.map (function p2tc -> p2tc :: p2tcs1) (patcst2_diff p2tc1 p2tc2) in
	let p2tcss2 =
	  List.map
	    (function p2tcs -> p2tc1 :: p2tcs) (patcst2_list_diff p2tcs1 p2tcs2) in
	  p2tcss1 @ p2tcss2
      end
    | _, _ -> error_of_deadcode "ats_pat2_complement: patcst2_list_diff"
(* end of [patcst2_list_diff] *)

(* ****** ****** *)

let cla2_pat_comp (c2l: cla2): patcst2 list list =
  match c2l.cla2_gua with
    | None -> begin
	let p2tcs = patcst2_of_pat2_list c2l.cla2_pat in
	  patcst2_list_comp p2tcs
      end
    | Some _ -> begin (* the most conservative estimation *)
	let p2tcs = List.map (function p2t -> PTC2any) c2l.cla2_pat in
	  [p2tcs]
      end
(* end of [cla2_pat_comp] *)

(* ****** ****** *)

(* end of [ats_patcst2.ml] *)
