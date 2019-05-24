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

(* ats_fm_solver: solve linear constraints
     with the Fourier-Motzkin variable elimination method. *)

(* The implementation is largely adopted from an earlier implementation for DML *)

open Ats_misc

module A = Array
module BI = Big_int
module PR = Printf

(* ****** ****** *)

type intvec = intinf array

type icstr =
  | ICeq of intvec
  | ICgte of intvec
  | IClt of intvec
  | ICneq of intvec
  | ICconj of icstr list
  | ICdisj of icstr list
(* end of [icstr] *)

let rec icstr_negate (ic: icstr): icstr = match ic with
  | ICeq v -> ICneq v
  | ICgte v -> IClt v
  | IClt v -> ICgte v
  | ICneq v -> ICeq v
  | ICconj ics -> ICdisj (icstr_list_negate ics)
  | ICdisj ics -> ICconj (icstr_list_negate ics)
(* end of [icstr_negate] *)

and icstr_list_negate (ics: icstr list): icstr list = List.map icstr_negate ics

(* ****** ****** *)

let fprint_intvec (out: out_channel) (v: intvec): unit =
  let n = A.length v in
  let rec aux (i: int): unit =
    if i < n then (PR.fprintf out "; %s" (string_of_intinf v.(i)); aux (i+1)) in
    if n > 0 then (PR.fprintf out "%s" (string_of_intinf v.(0)); aux 1)
(* end of [fprint_intvec] *)

let fprint_intvec_list
  (out: out_channel) (vs: intvec list): unit =
  fprint_list_with_sep fprint_intvec out vs "\n"

let rec fprint_icstr (out: out_channel) (ic: icstr): unit = match ic with
  | ICeq v -> PR.fprintf out "ICeq(%a)" fprint_intvec v
  | ICgte v -> PR.fprintf out "ICgte(%a)" fprint_intvec v
  | IClt v -> PR.fprintf out "IClt(%a)" fprint_intvec v
  | ICneq v -> PR.fprintf out "ICneq(%a)" fprint_intvec v
  | ICconj ics -> PR.fprintf out "ICconj(%a)" fprint_icstr_list ics
  | ICdisj ics -> PR.fprintf out "ICdisj(%a)" fprint_icstr_list ics
(* end of [fprint_icstr] *)

and fprint_icstr_list (out: out_channel) (ics: icstr list): unit =
  fprint_list_with_sep fprint_icstr out ics "\n"

(* ****** ****** *)

exception Tautology
exception Contradiction

let vec_inspect_gte (vec: intvec): unit =
  let n = A.length vec in
  let rec aux g i =
    if i = n then
      if intinf_is_zero g then
        if intinf_is_neg vec.(0) then raise Contradiction else raise Tautology
      else if intinf_is_unit g then ()
      else begin
	vec.(0) <- BI.div_big_int vec.(0) g;
	for i = 1 to n-1 do vec.(i) <-  BI.div_big_int vec.(i) g done
      end
    else aux (BI.gcd_big_int g (vec.(i))) (i+1) in
  aux intinf_zero 1 (* Notice: coefficients start at 1! *)
(* end of [vec_inspect_gte] *)

let vec_inspect_eq (vec: intvec): unit =
  let n = A.length vec in
  let rec aux g i =
    if i = n then
      if intinf_is_zero g then
        if intinf_is_zero vec.(0) then raise Tautology else raise Contradiction
      else begin
	if intinf_is_unit g then () else
	  let (q, r) = BI.quomod_big_int vec.(0) g in
	    if intinf_is_zero r then begin
	      vec.(0) <- q;
	      for i = 1 to n-1 do vec.(i) <- BI.div_big_int vec.(i) g done
	    end else raise Contradiction
      end
    else aux (BI.gcd_big_int g (vec.(i))) (i+1) in
    aux intinf_zero 1 (* Notice: coefficients start at 1! *)
(* end of [vec_inspect_eq] *)

(* ****** ****** *)

let vec_least_coef (vec: intvec): int = (* yields the least non zero coefficient *)
  let n = A.length vec in
  let rec aux i0 c0 i =
    if i < n && not (intinf_is_unit c0) then
      let i' = i and c' = BI.abs_big_int vec.(i) in
	if intinf_is_zero c' then aux i0 c0 (i+1)
	else if intinf_is_zero c0 then aux i' c' (i+1)
	else if BI.le_big_int c0 c' then aux i0 c0 (i+1)
	else aux  i' c' (i+1)
    else i0 in
    aux 0 intinf_zero 1
(* end of [vec_least_coef] *)

let vec_scalar (c: int) (vec: intvec): intvec =
  let n = A.length vec in
  let ans = A.make n intinf_zero in
  let () =
    for i = 0 to n-1 do
      ans.(i) <- BI.mult_int_big_int c vec.(i)
    done in ans
(* end of [vec_scalar] *)

let vec_add (c1: intinf) (v1: intvec) (c2: intinf) (v2: intvec): intvec =
  let n = A.length v1 in
  let ans = A.make n intinf_zero in
  let () =
    for i = 0 to n - 1 do
      ans.(i) <- 
      BI.add_big_int
	(BI.mult_big_int c1 v1.(i)) (BI.mult_big_int c2 v2.(i))
    done in ans
(* end of [vec_add] *)

let vec_combine (i: int) (neg: intvec) (pos: intvec) (vecs: intvec list)
  : intvec list =
  let vec = vec_add pos.(i) neg (BI.minus_big_int neg.(i)) pos in
  try let () = vec_inspect_gte vec in vec :: vecs
  with Tautology -> vecs
(* end of [vec_combine] *)

let vec_split i (vecs: intvec list): intvec list =
  let rec aux none_set neg_set pos_set = function
      [] -> (none_set, neg_set, pos_set)
    | vec :: rest ->
      if intinf_is_neg vec.(i) then aux none_set (vec :: neg_set) pos_set rest
      else if intinf_is_pos vec.(i) then aux none_set neg_set (vec :: pos_set) rest
           else aux (vec :: none_set) neg_set pos_set rest in
  let rec auxpos vecs neg = function
      [] -> vecs
    | pos :: rest -> auxpos (vec_combine i neg pos vecs) neg rest in
  let rec auxnegpos vecs pos_set = function
      [] -> vecs
    | neg :: rest -> auxnegpos (auxpos vecs neg pos_set) pos_set rest in
  let (none_set, neg_set, pos_set) = aux [] [] [] vecs in
    auxnegpos none_set pos_set neg_set
(* end of [vec_split] *)

(* ****** ****** *)

let solve_veclist (vs0: intvec list): unit =
(*
  let () =
    PR.fprintf stdout "solve_veclist: vs0 =\n%a\n" fprint_intvec_list vs0 in
*)
  let rec screen res = function
    | [] -> List.rev res
    | v :: vs ->
	try let () = vec_inspect_gte v in screen (v :: res) vs
	with Tautology -> screen res vs in
  let rec aux = function
    | [] -> ()
    | v :: _ as vs -> aux (vec_split (vec_least_coef v) vs) in
  aux (screen [] vs0)
(* end of [solve_veclist] *)

(*
external solve_veclist_simplex: string array list -> int = "caml_solve_veclist_simplex"
external solve_veclist_omega: string array list -> int = "caml_solve_veclist_omega"

let solve_veclist (vecs: intvec list): unit =
  let rec screen res = function
    | [] -> List.rev res
    | vec :: vecs ->
	try let _ = vec_inspect_gte vec in screen (vec :: res) vecs
	with Tautology -> screen res vecs in
  let vecs = 
    List.map (fun a -> Array.map string_of_intinf a) (screen [] vecs) in 
    match vecs with
      | [] -> ()
      | _ :: _ -> begin
	  let i = solve_veclist_omega vecs in
	    match i with
	      | -1 -> raise Contradiction
	      | -2 -> begin
		  let i2 = solve_veclist_simplex vecs in
		    match i2 with
		      | -1 -> raise Contradiction
		      | _ -> ()
		end
	      | _ -> ()
	end
*)
	  
exception UnsolvedConstraint of (int * intvec) list * intvec list

let vec_veceq_elim (v: intvec) (ve: intvec) (i: int): intvec =
(*
  let () =
    PR.fprintf stdout "vec_veceq_elim: v = %a\n" fprint_intvec v in
  let () =
    PR.fprintf stdout "vec_veceq_elim: ve = %a\n" fprint_intvec ve in
  let () =
    PR.fprintf stdout "vec_veceq_elim: i = %i\n" i in
*)
  let c = v.(i) and ce = ve.(i) in
    if intinf_is_pos ce then vec_add ce v (BI.minus_big_int c) ve
    else vec_add (BI.minus_big_int ce) v c ve
(* end of [vec_veceq_elim] *)

let veclist_veceq_elim (vs: intvec list) (ve: intvec) (i: int): intvec list =
  let rec aux res = function
    | v :: vs -> aux (vec_veceq_elim v ve i :: res) vs | [] -> res in
    aux [] vs
(* end of [veclist_veceq_elim] *)

let vec_veceqlist_elim (v: intvec) (ives: (int * intvec) list): intvec =
  let rec aux v = function
    | [] -> v
    | (i, ve) :: ives -> aux (vec_veceq_elim v ve i) ives in
    aux v ives
(* end of [vec_veceqlist_elim] *)

(* ****** ****** *)

let rec solve_icstrlist
  (ives: (int * intvec) list) (vs: intvec list) (ics: icstr list) =
(*
  let () = PR.fprintf stdout
    "solve_icstrlist: ics =\n%a\n" fprint_icstr_list ics in
*)
  match ics with
    | [] -> raise (UnsolvedConstraint (ives, vs))
    | ic :: ics -> begin match ic with
	| ICeq ve -> begin
	    let ve = vec_veceqlist_elim ve ives in
	      try
		let () = vec_inspect_eq ve in
		let i = vec_least_coef ve in
		let vs = veclist_veceq_elim vs ve i in
		  (solve_veclist vs; solve_icstrlist (ives @ [(i, ve)]) vs ics)
	      with Tautology -> solve_icstrlist ives vs ics
	  end
	| ICgte v ->
	    let v = vec_veceqlist_elim v ives in
	      (solve_veclist (v :: vs); solve_icstrlist ives (v :: vs) ics)
	| IClt v ->
	    let v = vec_scalar (-1) v in
	    let () = v.(0) <- BI.pred_big_int v.(0) in
	    let v = vec_veceqlist_elim v ives in
	      (solve_veclist (v :: vs); solve_icstrlist ives (v :: vs) ics)
	| ICneq v ->
	    let v1 = vec_scalar 1 v and v2 = vec_scalar (-1) v in
	    let () = v1.(0) <- BI.pred_big_int v1.(0)
	    and () = v2.(0) <- BI.pred_big_int v2.(0) in
	      solve_icstrlist_disj ives vs ics [ICgte v1; ICgte v2]
	| ICconj ics1 -> solve_icstrlist ives vs (ics1 @ ics)
	| ICdisj ics1 -> solve_icstrlist_disj ives vs ics ics1
    end
(* end of [solve_icstrlist] *)

and solve_icstrlist_disj
  (ives: (int * intvec) list) (vs: intvec list)
  (ics: icstr list) (ics_disj: icstr list): unit =
  match ics_disj with
    | [] -> raise Contradiction
    | ic_disj :: ics_disj -> begin
	try solve_icstrlist ives vs (ic_disj :: ics)
	with Contradiction ->
	  solve_icstrlist_disj ives vs ics ics_disj
      end
(* end of [solve_icstrlist_disj] *)

(* ****** ****** *)

(* end of [ats_solver_fm.ml] *)
