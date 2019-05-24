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

module Err = Ats_error
module Loc = Ats_location
module Syn = Ats_syntax

module PR = Printf

open Ats_misc
open Ats_staexp2
open Ats_staexp2_util
open Ats_stacst2
open Ats_dynexp2

(* ****** ****** *)

type loc = Loc.location

(* ****** ****** *)

let error (msg: string): 'a = Err.error ("ats_dynexp2_util: " ^ msg)

(* ****** ****** *)

let pat2_proofize (p2t: pat2): unit = begin
  List.iter (function d2v -> d2v.dvar2_is_proof <- true) p2t.pat2_dvs
end (* end of [pat2_proofize] *)

(* ****** ****** *)

let dcst2_eq (d2c1: dcst2) (d2c2: dcst2) = d2c1 == d2c2
let dcst2_neq (d2c1: dcst2) (d2c2: dcst2) = d2c1 != d2c2

(* ****** ****** *)

let dvar2_eq (d2v1: dvar2) (d2v2: dvar2) = d2v1 == d2v2
let dvar2_neq (d2v1: dvar2) (d2v2: dvar2) = d2v1 != d2v2

(* ****** ****** *)

let ditem2_list_overload_extend
  (d2is: ditem2 list) (d2i0: ditem2): ditem2 list =
  let rec auxcheck (d2is: ditem2 list): bool =
    match d2is with
      | d2i :: d2is -> begin match d2i0, d2i with
	  | DI2cst d2c0, DI2cst d2c ->
              if dcst2_eq d2c0 d2c then true else auxcheck (d2is)
	  | DI2var d2v0, DI2var d2v ->
              if dvar2_eq d2v0 d2v then true else auxcheck (d2is)
	  | _, _ -> auxcheck (d2is)
	end
      | [] -> false in
  let loaded = auxcheck (d2is) in
    if loaded then d2is else (d2i0 :: d2is)
(* end of [ditem2_list_overload_extend] *)

(* ****** ****** *)

let dexp2_is_lamvar (d2e: dexp2): bool =
  match d2e.dexp2_node with
    | DE2lam_dyn _ -> true
    | DE2var _ -> true
    | DE2char _ -> true
    | DE2int _ -> true
    | DE2string _ -> true
    | DE2top -> true
    | _ -> false
(* end of [dexp2_is_lamvar] *)

let rec dexp2_is_raised (d2e0: dexp2): bool =
  match d2e0.dexp2_node with
    | DE2ann_type (d2e, _) -> dexp2_is_raised d2e
    | DE2ann_seff (d2e, _) -> dexp2_is_raised d2e
    | DE2case (_, _, _, c2ls) -> cla2_list_is_raised c2ls
    | DE2if (_, _, d2e1, od2e2) -> begin match od2e2 with
	| Some d2e2 -> dexp2_is_raised d2e1 && dexp2_is_raised d2e2
	| None -> false
      end
    | DE2let (d2cs, d2e) -> dexp2_is_raised d2e
    | DE2loopexn i -> true
    | DE2raise _ -> true
    | DE2seq d2es -> dexp2_seq_is_raised d2es
    | _ -> false
(* end of [dexp2_is_raised] *)

and dexp2_seq_is_raised (d2es: dexp2 list): bool =
  let rec aux d2e0 d2es = match d2es with
    | [] -> dexp2_is_raised d2e0
    | d2e :: d2es -> aux d2e d2es in
    match d2es with
      | [] -> false
      | d2e :: d2es -> aux d2e d2es
(* end of [dexp2_seq_is_raised] *)

and cla2_is_raised (c2l: cla2): bool =
  c2l.cla2_isneg || dexp2_is_raised c2l.cla2_body

and cla2_list_is_raised (c2ls: cla2 list): bool =
  List.for_all cla2_is_raised c2ls

(* ****** ****** *)

let dvar2_is_linear (d2v: dvar2): bool = d2v.dvar2_linear >= 0
let dvar2_is_mutable (d2v: dvar2): bool =
  match d2v.dvar2_view with None -> false | Some _ -> true

let dvar2_is_proof (d2v: dvar2): bool = d2v.dvar2_is_proof
let dvar2_is_not_proof (d2v: dvar2): bool = not (d2v.dvar2_is_proof)

(* ****** ****** *)

let type_of_dvar2 loc0 (d2v: dvar2): sexp2 = match d2v.dvar2_type with
  | Some s2e -> s2e
  | None -> begin
      PR.eprintf "%a: type_of_dvar2: no type for <%a>.\n"
	Loc.fprint loc0 fprint_dvar2 d2v;
      Err.abort ();
    end
(* end of [type_of_dvar2] *)

let addr_of_dvar2 (d2v: dvar2): sexp2 = match d2v.dvar2_addr with
  | Some s2l -> s2l
  | None -> begin
      PR.eprintf "%a: addr_of_dvar2: no address for <%a>.\n"
	Loc.fprint d2v.dvar2_loc fprint_dvar2 d2v;
      Err.abort ();
    end
(* end of [addr_dvar2] *)

let dvar2_view_of_dvar2 (d2v: dvar2): dvar2 = match d2v.dvar2_view with
  | Some d2v_view -> d2v_view
  | None -> begin
      PR.eprintf "%a: view_of_dvar2: no view variable for <%a>.\n"
	Loc.fprint d2v.dvar2_loc fprint_dvar2 d2v;
      Err.abort ();
    end
(* end of [dvar2_view_of_dvar2] *)

let type_of_dvar2_ptr (d2v: dvar2): sexp2 =
  let d2v_view = dvar2_view_of_dvar2 d2v in
  let s2e_view = d2v_view.dvar2_master_type  in
    match At_viewt0ype_addr_view.un_make_exp s2e_view with
      | Some [s2e1; s2e2] -> s2e1
      | _ -> begin
	  PR.eprintf "%a: type_of_dvar2_ptr: no type for <%a>.\n"
	    Loc.fprint d2v.dvar2_loc fprint_dvar2 d2v;
	  Err.abort ();
	end
(* end of [type_of_dvar2_ptr] *)

(* ****** ****** *)

let statype2_dvar2_assoc (sty2: statype2) (d2v0: dvar2): sexp2 option =
  let rec aux = function
    | (d2v, os2e) :: rest -> begin
	match dvar2_is_mutable d2v with
	  | true -> begin
	      let d2v_view = dvar2_view_of_dvar2 d2v in
		if dvar2_eq d2v0 d2v_view then begin
		  match os2e with
		    | Some s2e ->
			let s2l = addr_of_dvar2 d2v in
			  Some (sexp2_at_viewt0ype_addr_view s2e s2l)
		    | None -> None
		end else aux rest
	    end
	  | false -> if dvar2_eq d2v0 d2v then os2e else aux rest
      end
    | [] -> None in
    aux sty2.statype2_body
(* end of [statype2_dvar2_assoc] *)

(* ****** ****** *)

let statype2_body_new (body: statype2_body): statype2_body =
  let aux (d2v, os2e) =
    match d2v.dvar2_view, d2v.dvar2_addr with
      | Some d2v_view, Some s2l ->
	  let os2e_view = match os2e with
	    | Some s2e -> Some (sexp2_at_viewt0ype_addr_view s2e s2l)
	    | None -> None in
	    (d2v_view, os2e_view)
      | _, _ -> (d2v, os2e) in
    List.map aux body
(* end of [statype2_body_new] *)

let statype2_new (sty: statype2): statype2 =
  let body = statype2_body_new sty.statype2_body in
    statype2_make sty.statype2_svs sty.statype2_gua sty.statype2_met body
(* end of [statype2_new] *)

let loopinv2_new (inv: loopinv2): loopinv2 =
  let arg_new = statype2_body_new inv.loopinv2_arg in
  let res_new = match inv.loopinv2_res with
    | None -> None | Some res -> Some (statype2_new res) in
    loopinv2_make inv.loopinv2_loc
      inv.loopinv2_svs inv.loopinv2_gua inv.loopinv2_met arg_new res_new
(* end of [loopinv2_new] *)

(* ****** ****** *)

let statype2_body_subst (sub: subst) (body: statype2_body): statype2_body =
  let aux (d2v, os2e) = match os2e with
    | None -> (d2v, None)
    | Some s2e -> (d2v, Some (sexp2_subst sub s2e)) in
  List.map aux body
(* end of [statype2_body_subst] *)

(* ****** ****** *)

let dcon2_select_with_arity (d2cs: dcon2 list) (n: int): dcon2 list =
  List.filter (function d2c -> d2c.dcon2_arity_full == n) d2cs

(* ****** ****** *)

let dexp2_lam_met_load (d2e0: dexp2) (d2vs_fun: dvar2 list): unit =
  let rec aux d2e0 =
    match d2e0.dexp2_node with
      | DE2lam_dyn (_, _, d2e) -> aux d2e
      | DE2lam_met (r, _, _) -> r := d2vs_fun
      | DE2lam_sta (_, _, d2e) -> aux d2e
      | _ -> () in
    aux d2e0
(* end of [dexp2_lam_met_load] *)

(* ****** ****** *)

let dexp2_var_is_ptr (d2e: dexp2): bool =
  let os2e = match d2e.dexp2_node with
    | DE2var d2v -> d2v.dvar2_type
    | _ -> error_of_deadcode
	"ats_dynexp2_util: dexp2_var_is_ptr" in
    match os2e with
      | Some s2e -> Ptr_addr_type.eq_exp (sexp2_whnf s2e)
      | None -> false
(* end of [dexp2_var_is_ptr] *)

let dexp2_var_is_arr (d2e: dexp2): bool =
  let os2e = match d2e.dexp2_node with
    | DE2var d2v -> d2v.dvar2_type
    | _ -> error_of_deadcode
	"ats_dynexp2_util: dexp2_var_is_ptr" in
    match os2e with
      | Some s2e -> sexp2_is_tyarr (sexp2_whnf s2e)
      | None -> false
(* end of [dexp2_var_is_arr] *)

(* ****** ****** *)

type lval2 =
  | LVAL2arrsub of (* array subscription *)
      dsym2 (* brackets overloading *) * dexp2 * dexp2 list list
  | LVAL2ptr of dexp2 * dlab2 list
  | LVAL2var_lin of dvar2 * dlab2 list
  | LVAL2var_mut of dvar2 * dlab2 list
  | LVAL2none of dexp2
(* end of [lval2] *)

let lval2_of_dexp2 (d2e0: dexp2): lval2 =
  match d2e0.dexp2_node with
    | DE2arrsub (d2s_brackets, d2e_arr, d2ess_ind) -> begin
	let is_ptr = dexp2_var_is_ptr d2e_arr in
	  if is_ptr then LVAL2ptr (d2e_arr, [dlab2_ind d2ess_ind])
	  else LVAL2arrsub (d2s_brackets, d2e_arr, d2ess_ind)
      end
    | DE2deref d2e -> LVAL2ptr (d2e, [])
    | DE2sel (d2e, d2ls) -> begin match d2e.dexp2_node with
	| DE2var d2v when dvar2_is_linear d2v -> LVAL2var_lin (d2v, d2ls)
	| DE2var d2v when dvar2_is_mutable d2v -> LVAL2var_mut (d2v, d2ls)
	| DE2deref d2e -> LVAL2ptr (d2e, d2ls)
	| _ -> LVAL2none d2e0
      end
    | DE2var d2v when dvar2_is_linear d2v -> LVAL2var_lin (d2v, [])
    | DE2var d2v when dvar2_is_mutable d2v -> LVAL2var_mut (d2v, [])
    | _ -> LVAL2none d2e0
(* end of [lval2_of_dexp2] *)

(* ****** ****** *)

let dexp2_sel_1 loc0 (is_ptr: int) (d2e0: dexp2) (d2l: dlab2) =
  if is_ptr > 0 then dexp2_selptr loc0 d2e0 d2l
  else begin match d2e0.dexp2_node with
    | DE2sel (d2e, d2ls) -> dexp2_sel loc0 d2e (d2ls @ [d2l])
    | _ -> dexp2_sel loc0 d2e0 [d2l]
  end (* end of [dexp2_sel_1] *)

(* ****** ****** *)

let dvar2_set_type (d2v: dvar2) (s2e: sexp2) = begin
  d2v.dvar2_linear <- d2v.dvar2_linear + 1; d2v.dvar2_type <- Some s2e;
end (* end of [dvar2_set_type] *)

let dvar2_set_type_at (d2v: dvar2) (s2e: sexp2) (s2l: sexp2) =
  let () = d2v.dvar2_linear <- d2v.dvar2_linear + 1 in
  let s2e = sexp2_whnf s2e in begin match s2e.sexp2_node with
    | SE2out _ -> d2v.dvar2_type <- None
    | _ when Void_t0ype.eq_exp s2e -> d2v.dvar2_type <- None
    | _ -> begin
	let s2e_view = sexp2_at_viewt0ype_addr_view s2e s2l in
	  d2v.dvar2_type <- Some s2e_view
      end 
    end
(* end of [dvar2_set_type_at] *)

(* ****** ****** *)

let dvar2_viewat_del_aux loc0
  (d2v_view: dvar2) (s2e_elt: sexp2) (s2l: sexp2) (s2labs: slab2 list)
  : sexp2 (* type *) * sexp2 list (* constraint *) * slab2 list =
  let (s2e_elt, s2e_old, s2ps, s2labs) = sexp2_select_list_del loc0 s2e_elt s2labs in
  let () = dvar2_set_type_at d2v_view s2e_elt s2l in
    (s2e_old, s2ps, s2labs)
(* end of [dvar2_viewat_del_aux] *)

let dvar2_viewat_del loc0 (d2v_view: dvar2) (s2labs: slab2 list)
  : sexp2 (* type *) * sexp2 list (* constraint *) * slab2 list =
  let s2e_view = match d2v_view.dvar2_type with
    | Some s2e -> s2e 
    | None -> begin
	PR.eprintf
	  "%a: dvar2_viewat_del: there is no view in <%a> for deletion.\n"
	  Loc.fprint loc0 fprint_dvar2 d2v_view;
	Err.abort ();
      end in
    match un_sexp2_at_viewt0ype_addr_view s2e_view with
      | Some (s2e_elt, s2l) -> dvar2_viewat_del_aux loc0 d2v_view s2e_elt s2l s2labs
      | None -> begin
	  PR.eprintf
	    "%a: dvar2_viewat_del: there is no viewat in <%a> for deletion.\n"
	    Loc.fprint loc0 fprint_dvar2 d2v_view;
	  Err.abort ();
	end
(* end of [dvar2_viewat_del] *)

(* ****** ****** *)

let dvar2_viewat_set_aux loc0 (d2v1_view: dvar2)
  (s2e1_elt: sexp2) (s2l1: sexp2) (s2labs0: slab2 list) (s2e2_new_at: sexp2)
  : sexp2 (* type *) * sexp2 list (* constraint *) * slab2 list =
  let (s2e2_new, s2l2) =
    let s2e2_new_at = sexp2_whnf s2e2_new_at in
      match un_sexp2_at_viewt0ype_addr_view s2e2_new_at with
	| Some (s2e, s2l) -> (s2e, s2l)
	| None -> begin
	    PR.eprintf "%a: dvar2_viewat_set_aux: not an viewat: <%a>.\n"
	      Loc.fprint loc0 fprint_sexp2 s2e2_new_at;
	    Err.abort ();
	  end in
  let () =
    let s2l1 = sexp2_proj_list s2l1 s2labs0 in
      if not (sexp2_syneq s2l1 s2l2) then begin
	PR.eprintf "%a: dvar2_viewat_set_aux: addresses mismatch: %a <> %a.\n"
	  Loc.fprint loc0 fprint_sexp2 s2l1 fprint_sexp2 s2l2;
	Err.abort ();
      end in
  let (s2e1_elt, s2e2_old, s2ps, s2labs) =
    sexp2_select_list_set loc0 s2e1_elt s2labs0 s2e2_new in
  let () = dvar2_set_type_at d2v1_view s2e1_elt s2l1 in
    (s2e2_old, s2ps, s2labs)
(* end of [dvar2_viewat_set_aux] *)

let dvar2_viewat_set loc0
  (d2v1_view: dvar2) (s2labs0: slab2 list) (s2e2_new_at: sexp2)
  : sexp2 (* type *) * sexp2 list (* constraint *) * slab2 list =
  match d2v1_view.dvar2_type with
    | None -> 
	let s2e1_elt = sexp2_void_t0ype () in
	let s2l1 = addr_of_dvar2 d2v1_view in
	  dvar2_viewat_set_aux loc0 d2v1_view s2e1_elt s2l1 s2labs0 s2e2_new_at
    | Some s2e -> begin match un_sexp2_at_viewt0ype_addr_view s2e with
	| Some (s2e1_elt, s2l1) ->
	    dvar2_viewat_set_aux loc0 d2v1_view s2e1_elt s2l1 s2labs0 s2e2_new_at
	| None -> begin
	    PR.eprintf
	      "%a: dvar2_viewat_set: there is no viewat in <%a> for update.\n"
	      Loc.fprint loc0 fprint_dvar2 d2v1_view;
	    Err.abort ();
	  end
      end
(* end of [dvar2_viewat_set] *)

(* ****** ****** *)

(* end of ats_dynexp2_util.ml *)
