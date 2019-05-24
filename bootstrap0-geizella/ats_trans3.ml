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

open Ats_misc

open Ats_staexp2
open Ats_staexp2_util
open Ats_stacst2
open Ats_dynexp2
open Ats_dynexp2_util
open Ats_dyncst2
open Ats_patcst2
open Ats_errmsg2
open Ats_dynexp3

open Ats_errmsg3
open Ats_trans3_pat

module P = Printf

module Cnt = Ats_counter
module Err = Ats_error
module Eff = Ats_effect
module Lab = Ats_label
module Loc = Ats_location
module Mac = Ats_macro
module Met = Ats_metric
module PFc = Ats_printf_c
module SB = Ats_svar_bind
module SS = Ats_svar_stamp
module Sym = Ats_symbol
module Syn = Ats_syntax

module SEnv3 = Ats_staenv3
module DEnv3 = Ats_dynenv3

module SOL = Ats_staexp2_solve

(* ****** ****** *)

type lab = Lab.label
type loc = Loc.location
type symbol = Sym.symbol

(* two standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_trans3: "; Err.error s;
end

let error_with_loc (loc: loc) (s: string): 'a = begin
  prerr_string "ats_trans3: "; Err.error_with_loc loc s;
end

(* ****** ****** *)

let dexp2_funclo_of_dexp2 (d2e0: dexp2): dexp2 * Syn.funclo =
  match d2e0.dexp2_node with
    | DE2ann_funclo (d2e, fc) -> (d2e, fc) | _ -> (d2e0, Syn.FUNCLOfun)

let dexp2_funclo_opt_of_dexp2 (d2e0: dexp2)
  : dexp2 * Syn.funclo option = match d2e0.dexp2_node with
    | DE2ann_funclo (d2e, fc) -> (d2e, Some fc) | _ -> (d2e0, None)

let seff2_of_dexp2 (d2e0: dexp2): seff2 =
  match d2e0.dexp2_node with
    | DE2ann_seff (_, sf2e) -> sf2e
    | DE2lam_dyn _ -> seff2_nil
    | DE2lam_sta _ -> seff2_nil
    | _ -> seff2_all

let dexp2_seff2_of_dexp2 (d2e0: dexp2): dexp2 * seff2 =
  match d2e0.dexp2_node with
    | DE2ann_seff (d2e, sf2e) -> (d2e, sf2e)
    | DE2lam_dyn _ -> (d2e0, seff2_nil)
    | DE2lam_sta _ -> (d2e0, seff2_nil)
    | _ -> (d2e0, seff2_all)

let dexp2_seff2_opt_of_dexp2 (d2e0: dexp2)
  : dexp2 * seff2 option = match d2e0.dexp2_node with
    | DE2ann_seff (d2e, sf2e) -> (d2e, Some sf2e)
    | _ -> (d2e0, None)

exception Exn_type_of_dexp2

let rec type_of_dexp2 (d2e0: dexp2): sexp2 =
  match d2e0.dexp2_node with 
    | DE2ann_type (_, s2e) -> s2e
    | DE2ann_seff (d2e, _) -> type_of_dexp2 d2e
    | DE2ann_funclo (d2e, _) -> type_of_dexp2 d2e
    | DE2assgn _ -> sexp2_void_t0ype ()
    | DE2char c -> sexp2_char_char_t0ype c
    | DE2cst d2c -> d2c.dcst2_type
    | DE2effmask (_, d2e) -> type_of_dexp2 d2e
    | DE2empty -> sexp2_void_t0ype ()
    | DE2fix (_, d2e) -> type_of_dexp2 d2e
    | DE2float _ -> Double_t0ype.make_exp None
    | DE2for _ -> sexp2_void_t0ype ()
    | DE2int (ik, i) -> sexp2_int_t0ype_with_kind ik i
    | DE2lam_dyn (is_lin, (npf, p2ts), d2e) -> begin
(*
	let () =
	  P.fprintf stdout "type_of_dexp2: DE2lam_dyn: d2e = %a\n"
	    fprint_dexp2 d2e in
*)
	let s2es_arg = type_of_pat2_list p2ts in
	let s2e_res = type_of_dexp2 d2e in
	let (d2e, fc) = dexp2_funclo_of_dexp2 d2e in
	let sf2e = seff2_of_dexp2 d2e in
	let is_prf = sexp2_is_proof s2e_res in
        let s2t_fun = srt2_fun_lin_prf is_lin is_prf in
	let lin = if is_lin then 1 else 0 in
	let s2e_funclo =
	  sexp2_funclo_with_sort s2t_fun fc lin sf2e (npf, s2es_arg) s2e_res in
(*
	let () =
	  P.fprintf stdout "type_of_dexp2: DE2lam_dyn: s2e_fun = %a\n"
	    fprint_sexp2 s2e_fun in
*)
	  s2e_funclo

      end
    | DE2lam_met (r, s2es, d2e) -> begin match !r with
	| _ :: _ -> sexp2_mfun None s2es (type_of_dexp2 d2e)
	| [] -> begin
	    P.eprintf "%a: illegal use of termination metric.\n"
	      Loc.fprint d2e0.dexp2_loc;
	    Err.abort ();
	  end
      end
    | DE2lam_sta (s2vs, s2ps, d2e) ->
	let () = SEnv3.SS.push () in
	let () = SEnv3.SS.svar_list_add s2vs in
	let s2e = sexp2_uni s2vs s2ps (type_of_dexp2 d2e) in
	let () = SEnv3.SS.pop () in
	  s2e
    | DE2let (_, d2e) -> type_of_dexp2 d2e
    | DE2string s -> sexp2_string_int_type s
    | DE2while _ -> sexp2_void_t0ype ()
    | _ -> begin
	let s2e = SEnv3.sexp2_VarApp_new d2e0.dexp2_loc srt2_t0ype in
	let () = d2e0.dexp2_type <- Some s2e in
	  s2e
      end

and type_of_dexp2_seq (d2es: dexp2 list): sexp2 =
  let rec aux d2e d2es = match d2es with
    | [] -> type_of_dexp2 d2e
    | d2e :: d2es -> aux d2e d2es in
    match d2es with
      | [] -> sexp2_void_t0ype ()
      | d2e :: d2es -> aux d2e d2es

(* ****** ****** *)

let type_of_dexp3 (d3e: dexp3): sexp2 = d3e.dexp3_type
let type_of_dexp3_list (d3es: dexp3 list): sexp2 list =
  List.map type_of_dexp3 d3es
let type_of_labdexp3 ((l,d3e): labdexp3): labsexp2 =
  (l, d3e.dexp3_type)
let type_of_labdexp3_list (ld3es: labdexp3 list): labsexp2 list =
  List.map type_of_labdexp3 ld3es

let skexp2_of_dexp3 (d3e: dexp3): skexp2= skexp2_of_sexp2 d3e.dexp3_type

(* ****** ****** *)

let dvar2_open_and_add (d2v: dvar2): unit = match d2v.dvar2_type with
    | Some s2e ->
	let s2e = SEnv3.sexp2_open_and_add s2e in d2v.dvar2_type <- Some s2e
    | None -> ()

let dexp3_open_and_add (d3e: dexp3): unit =
  let s2e = SEnv3.sexp2_open_and_add d3e.dexp3_type in
    d3e.dexp3_type <- s2e

let dexp3_list_open_and_add (d3es: dexp3 list): unit =
  List.iter dexp3_open_and_add d3es

let dexp23_open_and_add (d23e: dexp23): unit = match d23e with
  | DE23dexp2 _ -> ()
  | DE23dexp3 d3e -> dexp3_open_and_add d3e

let dexp23_arg_list_open_and_add (d23es: dexp23 list): unit = 
  List.iter dexp23_open_and_add d23es

(* ****** ****** *)

let fprint_ditem2_xyz (out: out_channel) (d3e, _, _) =
  fprint_dexp3 out d3e

let fprint_ditem2_xyzs (out: out_channel) xyzs =
  fprint_list_with_sep fprint_ditem2_xyz out xyzs ", "

let ditem2_list_sort_args (* a highly technical function *)
  (xyzs: (dexp3 * skexp2 * skexp2 list list) list)
  : (dexp3 * skexp2 * skexp2 list list) list =
  let rec aux1 xyz0 skss0 xyzs1 = function
    | [] -> xyz0 :: List.rev (xyzs1)
    | ((_, _, skss) as xyz) :: xyzs2 -> begin
(*
	let () =
	  P.fprintf stdout "skss0 = %a\nskss = %a\n"
	    fprint_skexp2_list_list skss0
	    fprint_skexp2_list_list skss in
*)
	if skexp2_list_list_leq skss0 skss then
	  if skexp2_list_list_leq skss skss0 then
	    aux1 xyz0 skss0 (xyz :: xyzs1) xyzs2
	  else aux1 xyz0 skss0 xyzs1 xyzs2
	else if skexp2_list_list_leq skss skss0 then
	  List.rev_append xyzs1 (xyz :: xyzs2)
	else aux1 xyz0 skss0 (xyz :: xyzs1) xyzs2
      end in
  let rec aux2 xyzs1 = function
    | [] -> List.rev xyzs1
    | ((_, _, skss) as xyz) :: xyzs2 ->
	aux2 (aux1 xyz skss [] xyzs1) xyzs2 in
    aux2 [] xyzs

let ditem2_list_select_args
  (sks0: skexp2 list)
  (xyzs: (dexp3 * skexp2 * skexp2 list list) list)
  : (dexp3 * skexp2 * skexp2 list list) list =
(*
  let () = 
    P.fprintf stdout "ditem2_list_select_args: sks0 = %a\n"
      fprint_skexp2_list sks0 in
*)
  let rec aux res = function
    | [] -> List.rev res
    | (d3e, sk, skss) :: xyzs -> begin
(*
	let () =
	  P.eprintf "ditem2_list_select_args: aux: d3e = %a and sk = %a\n"
	    fprint_dexp3 d3e fprint_skexp2 sk in
*)
	match skexp2_match_args sk sks0 with
	  | None -> aux res xyzs
	  | Some (sks_arg, sk_res) ->
	      aux ((d3e, sk_res, sks_arg :: skss) :: res) xyzs
      end in
    aux [] xyzs

(* ****** ****** *)

let dexp3_sexp2_int (d3e: dexp3): sexp2 =
  let s2e = sexp2_whnf d3e.dexp3_type in
    match un_sexp2_int_int_t0ype s2e with
      | Some s2i -> s2i
      | None -> begin
	  P.eprintf "%a: dexp3_sexp2_int: not an integer type: %a\n"
	    Loc.fprint d3e.dexp3_loc fprint_sexp2 s2e;
	  Err.abort ();
	end

(* ****** ****** *)

let slab2_of_dlab3_nt_list (d3labs0_nt: dlab3_nt list): slab2 list =
  let rec aux res = function
    | d3lab_nt :: d3labs_nt -> begin
	let res =
	  match d3lab_nt.dlab3_nt_lab with
	    | Some l -> slab2_lab0 l :: res | None -> res in
	  match d3lab_nt.dlab3_nt_ind with
	    | Some d3ess ->
		let s2ess =
		  List.map (List.map dexp3_sexp2_int) d3ess in
		  aux (slab2_ind0 s2ess :: res) d3labs_nt
	    | None -> aux res d3labs_nt
      end
    | [] -> List.rev res in
    aux [] d3labs0_nt

let slab2_of_dlab3_list (d3labs0: dlab3 list): slab2 list =
  let rec aux res = function
    | d3lab :: d3labs -> begin
	let res =
	  match d3lab.dlab3_lab with
	    | Some (l, s2e_rec) ->
		slab2_lab1 l s2e_rec :: res | None -> res in
	  match d3lab.dlab3_ind with
	    | Some (d3ess, s2e_elt) ->
		let s2ess =
		  List.map (List.map dexp3_sexp2_int) d3ess in
		  aux (slab2_ind1 s2ess s2e_elt :: res) d3labs
	    | None -> aux res d3labs
      end
    | [] -> List.rev res in
    aux [] d3labs0

(* ****** ****** *)

let dlab3_of_dlab3_nt_slab2_list
  (d3labs_nt: dlab3_nt list) (s2labs: slab2 list): dlab3 list =
  let rec aux d3labs d3labs_nt s2labs = match d3labs_nt with
    | d3lab_nt :: d3labs_nt -> begin
	let (olab, s2labs) = match d3lab_nt.dlab3_nt_lab with
	  | Some l -> begin match s2labs with
	      | SL2lab1 (_, s2e_rec) :: s2labs -> (Some (l, s2e_rec), s2labs)
	      | _ -> error_of_deadcode "ats_trans3: dlab3_of_dlab3_nt_slab2_list"
	    end
	  | None -> (None, s2labs) in
	let (oind, s2labs) = match d3lab_nt.dlab3_nt_ind with
	  | Some d3ess -> begin match s2labs with
	      | SL2ind1 (_, s2e_elt) :: s2labs -> (Some (d3ess, s2e_elt), s2labs)
	      | _ -> error_of_deadcode "ats_trans3: dlab3_of_dlab3_nt_slab2_list"
	    end
	  | None -> (None, s2labs) in
	let d3lab = dlab3_olab_oind olab oind in
	  aux (d3lab :: d3labs) d3labs_nt s2labs
      end
    | [] -> List.rev d3labs in
    aux [] d3labs_nt s2labs

(* ****** ****** *)

let dexp3_sel_tr_up loc0 (d3e0: dexp3) (d3labs_nt: dlab3_nt list): dexp3 =
  match d3labs_nt with
    | _ :: _ -> begin
	let () = dexp3_open_and_add d3e0 in
	let s2labs_nt = slab2_of_dlab3_nt_list d3labs_nt in
	let (s2e, is_lin, s2labs) =
	  sexp2_select_list loc0 d3e0.dexp3_type s2labs_nt in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	let () =
	  if is_lin then begin
	    P.eprintf "%a: dexp3_sel_tr_up: linear selection\n" Loc.fprint loc0;
	    Err.abort ();
	  end in
	  dexp3_sel loc0 s2e d3e0 d3labs
      end
    | [] -> d3e0

(* ****** ****** *)

let rec dexp3_tr_dn d3e s2e: unit =
(*
  let () = P.fprintf stdout "dexp3_tr_dn: \n" in
  let () =
    P.fprintf stdout "  d3e.dexp3_type = %a\n" fprint_sexp2 (d3e.dexp3_type) in
  let () = P.fprintf stdout "  s2e = %a\n" fprint_sexp2 s2e in
*)
  SOL.sexp2_tyleq_solve d3e.dexp3_loc d3e.dexp3_type s2e

(* ****** ****** *)

let sexp2_select_list_set_extra loc0
  (s2e: sexp2) (s2labs: slab2 list) (s2e_new: sexp2)
  : sexp2 (* type/whole *) *
    sexp2 (* type/part *) *
    sexp2 list (* cstr *) *
    slab2 list =
  let is_subscript = slab2_list_is_subscript s2labs in
    if is_subscript then begin
      let (s2e, s2e_old, s2ps, s2labs) as result =
	sexp2_select_list_get loc0 s2e s2labs in
      let () = SOL.sexp2_tyleq_solve loc0 s2e_new s2e_old in
	result
    end else begin
      sexp2_select_list_set loc0 s2e s2labs s2e_new
    end

let addr_assgn_sel loc0
  (s2l0: sexp2) (s2labs0: slab2 list) (s2e_new: sexp2): slab2 list =
  let (s2r0, s2labs0_ft) = sexp2_addr_norm s2l0 in
  let s2labs0 = s2labs0_ft @ s2labs0 in begin
      match DEnv3.dvar2_viewat_find s2r0 s2labs0 with
	| Some (d2v_view, s2e_elt, s2l, s2labs_ft, s2labs_bk) ->
	    let _ (* is_local_llam *) = DEnv3.dvar2_is_local_llam d2v_view in
	    let (s2e_elt, s2e_old, s2ps, s2labs_bk) =
	      sexp2_select_list_set_extra loc0 s2e_elt s2labs_bk s2e_new in
(*
	    let () = P.fprintf stdout "addr_assgn_sel: d2v_view = %a\n" fprint_dvar2 d2v_view in
	    let () = P.fprintf stdout "addr_assgn_sel: s2e_elt = %a\n" fprint_sexp2 s2e_elt in
	    let () = P.fprintf stdout "addr_assgn_sel: s2e_old = %a\n" fprint_sexp2 s2e_old in
*)
	    let s2labs0_bk = slab2_list_trim s2labs0_ft s2labs_ft s2labs_bk in
	    let () = SEnv3.prop_list_add loc0 s2ps in
	    let () = SOL.sexp2_szeqeq_solve loc0 s2e_new s2e_old in
	    let () = dvar2_set_type_at d2v_view s2e_elt s2l in
	    let () =
	      if sexp2_is_linear s2e_old then
		assgn_lintype_discard_errmsg loc0 s2e_old in
	      s2labs0_bk
	| None -> addr_assgn_no_viewat_errmsg loc0 s2r0 s2labs0
    end

let dvar2_lin_assgn_sel loc0
  (d2v: dvar2) (s2labs: slab2 list) (s2e_new: sexp2): slab2 list =
  let s2e_var = match d2v.dvar2_type with
    | None -> sexp2_void_t0ype () | Some s2e -> s2e in
  let (s2e_var, s2e_old, s2ps, s2labs) =
    sexp2_select_list_set_extra loc0 s2e_var s2labs s2e_new in
  let () = SEnv3.prop_list_add loc0 s2ps in
  let () =
    if sexp2_is_linear s2e_old then
      assgn_lintype_discard_errmsg loc0 s2e_old in
    begin
      d2v.dvar2_linear <- d2v.dvar2_linear + 1;
      d2v.dvar2_type <- Some s2e_var;
      s2labs
    end

let dvar2_mut_assgn_sel loc0
  (d2v: dvar2) (s2labs: slab2 list) (s2e_new: sexp2): slab2 list =
  let s2l = match d2v.dvar2_addr with
    | Some s2l -> s2l
    | None -> error_of_deadcode "ats_trans3: dvar2_mut_assgn_sel" in
    addr_assgn_sel loc0 s2l s2labs s2e_new

(* ****** ****** *)

let addr_viewat_get loc0 (s2l0: sexp2) (s2labs0: slab2 list)
  : sexp2 * slab2 list * dvar2 * slab2 list =
  let (s2r0, s2labs0_ft) = sexp2_addr_norm s2l0 in
  let s2labs0 = s2labs0_ft @ s2labs0 in
    match DEnv3.dvar2_viewat_find s2r0 s2labs0 with
      | Some (d2v_view, s2e_elt, s2l, s2labs_ft, s2labs_bk) ->
	  let (s2e_old, s2ps, s2labs_bk) =
	    dvar2_viewat_del_aux loc0 d2v_view s2e_elt s2l s2labs_bk in
	  let () = SEnv3.prop_list_add loc0 s2ps in
	  let s2labs0_bk = slab2_list_trim s2labs0_ft s2labs_ft s2labs_bk in
	  let s2e_at =
	    sexp2_at_viewt0ype_addr_view s2e_old (sexp2_proj_list s2l0 s2labs0_bk) in
	    (s2e_at, s2labs0_bk, d2v_view, s2labs_bk)
      | None -> begin
	  P.eprintf "%a: addr_viewat_get: there is no view at <%a>."
	    Loc.fprint loc0 fprint_sexp2 s2l0;
	  Err.abort ();
	end

let dvar2_mut_viewat_get loc0 (d2v: dvar2) (s2labs: slab2 list)
  : sexp2 * slab2 list * dvar2 * slab2 list =
  let s2l =  match d2v.dvar2_addr with
    | Some s2l -> s2l
    | None -> error_of_deadcode "ats_trans3: dvar2_mut_viewat_get" in
    addr_viewat_get loc0 s2l s2labs

(* ****** ****** *)

let addr_viewat_set loc0
  (s2l1: sexp2) (s2labs0: slab2 list) (s2e2_new: sexp2): slab2 list  =
  let (s2e2_elt, s2l2) =
    match un_sexp2_at_viewt0ype_addr_view s2e2_new with
      | Some (s2e_elt, s2l) -> (s2e_elt, s2l)
      | None -> begin
	  P.eprintf "%a: addr_viewat_set: no viewat: <%a>.\n"
	    Loc.fprint loc0 fprint_sexp2 s2e2_new;
	  Err.abort ();
	end in
  let (s2r1, s2labs0_ft) = sexp2_addr_norm s2l1 in
  let s2labs0 = s2labs0_ft @ s2labs0 in
  let () =
    let (s2r2, s2labs2) = sexp2_addr_norm s2l2 in
      if not (sexp2_syneq s2r1 s2r2 &&
	      slab2_list_synleq s2labs2 s2labs0) then begin
	P.eprintf
	  "%a: addr_viewat_set: addresses mismatch: %a <> %a.\n"
	  Loc.fprint loc0 fprint_sexp2 s2l1 fprint_sexp2 s2l2;
	Err.abort ();
      end in
    match DEnv3.dvar2_viewat_find s2r1 s2labs0 with
      | Some (d2v1_view, s2e1_elt, s2l1, s2labs1_ft, s2labs1_bk) ->
	  let _ (* is_local_llam *) = DEnv3.dvar2_is_local_llam d2v1_view in
	  let (s2e1_elt, s2e1_old, s2ps, s2labs1_bk) =
	    sexp2_select_list_set_extra loc0 s2e1_elt s2labs1_bk s2e2_elt in
	  let s2labs0_bk = slab2_list_trim s2labs0_ft s2labs1_ft s2labs1_bk in
	  let () = SEnv3.prop_list_add loc0 s2ps in
	  let () = dvar2_set_type_at d2v1_view s2e1_elt s2l1 in
	  let () = SOL.sexp2_void_solve loc0 s2e1_old in
	    s2labs0_bk
      | None -> begin
	  P.eprintf "%a: addr_viewat_set: no viewat: %a(%a).\n"
	    Loc.fprint loc0 fprint_sexp2 s2r1 fprint_slab2_list s2labs0;
	  Err.abort ();
	end

let dvar2_mut_viewat_set loc0
  (d2v1: dvar2) (s2labs0: slab2 list) (s2e2_new: sexp2): slab2 list =
  let s2l1 =  match d2v1.dvar2_addr with
    | Some s2l -> s2l
    | None -> error_of_deadcode "ats_trans3: dvar2_mut_viewat_set" in
    addr_viewat_set loc0 s2l1 s2labs0 s2e2_new

(* ****** ****** *)

let addr_deref_sel loc0
  (s2l0: sexp2) (s2labs0: slab2 list): sexp2 * slab2 list =
  let (s2r0, s2labs0_ft) = sexp2_addr_norm s2l0 in
  let s2labs0 = s2labs0_ft @ s2labs0 in
    match DEnv3.dvar2_viewat_find s2r0 s2labs0 with
      | Some (d2v_view, s2e_elt, s2l, s2labs_ft, s2labs_bk) ->
	  let _ (* is_local_llam *) = DEnv3.dvar2_is_local_llam d2v_view in
	  let (s2e_elt, s2e, s2ps, s2labs_bk) =
	    sexp2_select_list_get loc0 s2e_elt s2labs_bk in
(*
          let () = P.fprintf stdout "addr_deref_sel: d2v_view = %a\n" fprint_dvar2 d2v_view in
	  let () = P.fprintf stdout "addr_deref_sel: s2e_elt = %a\n" fprint_sexp2 s2e_elt in
	  let () = P.fprintf stdout "addr_deref_sel: s2e = %a\n" fprint_sexp2 s2e in
*)
	  let _ (* s2labs0_bk *) = slab2_list_trim s2labs0_ft s2labs_ft s2labs_bk in
          let () = SEnv3.prop_list_add loc0 s2ps in
	  let () =
	    if sexp2_is_linear s2e then dvar2_set_type_at d2v_view s2e_elt s2l in
	    (s2e, s2labs_bk)
      | None -> addr_deref_no_viewat_errmsg loc0 s2l0 s2labs0

let dvar2_mut_deref_sel loc0
  (d2v: dvar2) (s2labs: slab2 list): sexp2 * slab2 list =
  let s2l =  match d2v.dvar2_addr with
    | Some s2l -> s2l
    | None -> error_of_deadcode "ats_trans3: dvar2_mut_assgn_sel" in
    addr_deref_sel loc0 s2l s2labs

(* ****** ****** *)

let addr_probe_sel loc0
  (s2l0: sexp2) (s2labs0: slab2 list): slab2 list =
  let (s2r0, s2labs0_ft) = sexp2_addr_norm s2l0 in
  let s2labs0 = s2labs0_ft @ s2labs0 in
    match DEnv3.dvar2_viewat_find s2r0 s2labs0 with
      | Some (d2v_view, s2e_elt, s2l, s2labs_ft, s2labs_bk) ->
	  let (s2ps, s2labs_bk) =
	    sexp2_select_list_probe loc0 s2e_elt s2labs_bk in
	  let _ (* s2labs0_bk *) = slab2_list_trim s2labs0_ft s2labs_ft s2labs_bk in
          let () = SEnv3.prop_list_add loc0 s2ps in
	    s2labs_bk
      | None -> addr_probe_no_viewat_errmsg loc0 s2l0 s2labs0

let dvar2_mut_probe_sel loc0
  (d2v: dvar2) (s2labs: slab2 list): slab2 list =
  let s2l =  match d2v.dvar2_addr with
    | Some s2l -> s2l
    | None -> error_of_deadcode "ats_trans3: dvar2_mut_assgn_sel" in
    addr_probe_sel loc0 s2l s2labs

(* ****** ****** *)

let dexp3_lval_type_update (loc0)
  (refval: int) (d3e0: dexp3) (s2e_new: sexp2): int(*err*) = begin
  match d3e0.dexp3_node with
    | DE3sel_ptr (d3e_ptr, d3labs) -> begin
	match un_sexp2_ptr_addr_type d3e_ptr.dexp3_type with
	  | Some s2l ->
	      let s2labs = slab2_of_dlab3_list d3labs in
	      let _ (* s2labs *) =
		addr_assgn_sel loc0 s2l s2labs s2e_new in 0
	  | None -> error_of_deadcode "ats_trans3: dexp3_type_update"
      end
    | DE3sel_var (d2v, d3labs) when dvar2_is_linear d2v -> begin
	if refval = 0 then
	  let s2labs = slab2_of_dlab3_list d3labs in
	  let _ (* s2labs *) =
	    dvar2_lin_assgn_sel loc0 d2v s2labs s2e_new in 0
	else begin (* refval = 1 *)
	  P.eprintf "%a: the dynamic expression needs to be a left value.\n"
	    Loc.fprint d3e0.dexp3_loc;
	  Err.abort ();	  
	end
      end
    | DE3var d2v when dvar2_is_linear d2v -> begin
	if refval = 0 then
	  if d2v.dvar2_is_fixed (*fundec*) then 1(*err*) else begin
	    let _ (* s2labs *) = dvar2_lin_assgn_sel loc0 d2v [] s2e_new in 0
	  end
	else begin (* refval = 1 *)
	  P.eprintf "%a: the dynamic expression needs to be a left value.\n"
	    Loc.fprint d3e0.dexp3_loc;
	  Err.abort ();
	end
      end
    | DE3sel_var (d2v, d3labs) when dvar2_is_mutable d2v ->
	let s2labs = slab2_of_dlab3_list d3labs in
	let _ (* s2labs *) =
	  dvar2_mut_assgn_sel loc0 d2v s2labs s2e_new in 0
    | DE3var d2v when dvar2_is_mutable d2v ->
	let _ (* s2labs *) = dvar2_mut_assgn_sel loc0 d2v [] s2e_new in 0
    | DE3viewat_ptr (d3e, d3labs, d2v_view, s2labs_view) ->
	let (s2e_old, s2ps, s2labs_view) =
	  dvar2_viewat_set loc0 d2v_view s2labs_view s2e_new in
	let () = SEnv3.prop_list_add loc0 s2ps in
	let () = SOL.sexp2_void_solve loc0 s2e_old in 0
    | DE3viewat_var (d2v, d3labs, d2v_view, s2labs_view) ->
	let (s2e_old, s2ps, s2labs_view) =
	  dvar2_viewat_set loc0 d2v_view s2labs_view s2e_new in
	let () = SEnv3.prop_list_add loc0 s2ps in
	let () = SOL.sexp2_void_solve loc0 s2e_old in 0
    | _ -> begin
	if refval = 0 then begin
	  let s2e0 = d3e0.dexp3_type in if sexp2_is_linear s2e0 then 1 else 0
	end else begin
	  1 (* error *)
	end
      end
end (* end of [dexp3_lval_type_update] *)

let sexp2_is_freeptr (s2e: sexp2): bool = begin
  match s2e.sexp2_node with
    | SE2clo (knd, s2e_fun) ->
	if knd > 0 then
	  (if sexp2_is_linear s2e_fun then false else true)
	else false
    | _ -> false
end (* end of [sexp2_is_freeptr] *)

let dexp3_lval_type_update_arg
  (refval: int) (d3e0: dexp3) (s2e_new: sexp2): int(*freeknd*) = begin
  let loc0 = d3e0.dexp3_loc in
  let err = dexp3_lval_type_update loc0 refval d3e0 s2e_new in
    if err > 0 then begin match s2e_new with
      | _ when sexp2_is_freeptr s2e_new -> 1 (*freeknd*)
      | _ -> begin
	  P.eprintf "%a: the dynamic expression needs to be a left value.\n"
	    Loc.fprint loc0;
	  Err.abort ()
	end
    end else begin
      0 (*freeknd*)
    end
end (* end of [dexp3_lval_type_update] *)

let dexp3_lval_type_update_pat3 (d3e0: dexp3) (p3t: pat3): unit = begin
  match p3t.pat3_type_left with
    | Some s2e ->
	let loc0 = d3e0.dexp3_loc in
	let err = dexp3_lval_type_update loc0 0(*refval*) d3e0 s2e in
	  if err > 0 then begin
	    P.eprintf "%a: the dynamic expression needs to be a left value.\n"
	      Loc.fprint loc0;
	    Err.abort ()
	  end
    | None -> ()
end (* end of [dexp3_lval_type_update_pat3] *)

let dexp3_restore_fun_main (d3e: dexp3): dexp3 = begin
  let loc = d3e.dexp3_loc in
  let s2e = d3e.dexp3_type in
(*
  let () =
    P.fprintf stdout "dexp3_restore_fun_main: s2e = %a\n" fprint_sexp2 s2e in
*)
    match s2e.sexp2_node with
    | SE2clo (knd, s2e_fun) when knd >= 0 (*clo(0) or cloptr(1)*) ->
	let s2e_new =
	  if sexp2_is_linear s2e_fun then
	    sexp2_clo_with_sort srt2_viewtype knd (sexp2_topize s2e_fun)
	  else s2e in
	let refval = if knd > 0 then 0 (*cloptr*) else 1 (*clo*) in
        let freeknd = dexp3_lval_type_update_arg refval d3e s2e_new in
	  dexp3_refarg loc s2e refval freeknd d3e
    | _ -> d3e
end (* end of [dexp3_restore_fun_main] *)

let dexp3_restore_fun (d3e: dexp3): dexp3 = begin
  let isfixvar = match d3e.dexp3_node with
    | DE3var d2v -> d2v.dvar2_is_fixed | _ -> false in
    if isfixvar then d3e else dexp3_restore_fun_main d3e
end (* end of [dexp3_restore_fun] *)

(* d3es0 and s2es0 are assumed to be of the same length *)
let rec dexp3_list_restore_arg
  (d3es: dexp3 list) (s2es: sexp2 list): dexp3 list = begin
  match d3es, s2es with
    | d3e :: d3es, s2e :: s2es -> begin
	let d3e_new = match s2e.sexp2_node with
	  | SE2refarg (refval, _(*s2e_arg*), s2e_res) ->
	      let loc = d3e.dexp3_loc in
	      let s2e_res = SEnv3.sexp2_open_and_add s2e_res in
	      let freeknd = dexp3_lval_type_update_arg refval d3e s2e_res in
		dexp3_refarg loc s2e refval freeknd d3e
	  | _ -> d3e in
	  d3e_new :: (dexp3_list_restore_arg d3es s2es)
      end
    | _, _ -> []
end (* end of [dexp3_list_restore_arg] *)

(* ****** ****** *)

let rec dexp2_tr_up (d2e0: dexp2): dexp3 =
(*
  let () =
    P.fprintf stdout "dexp2_tr_up: before: d2e0 = %a\n"
      fprint_dexp2 d2e0 in
  let () =
    P.fprintf stdout "dexp2_tr_up: before: stamps = (%a)\n"
      fprint_stamps (SS.stamps_get ()) in
*)
  let d3e0 = dexp2_tr_up_main d2e0 in
  let s2e0 = d3e0.dexp3_type in
(*
  let () =
    P.fprintf stdout "dexp2_tr_up: after: d2e0 = %a\n"
      fprint_dexp2 d2e0 in
  let () =
    P.fprintf stdout "dexp2_tr_up: after: stamps = (%a)\n"
      fprint_stamps (SS.stamps_get ()) in
  let () =
    P.fprintf stdout "dexp2_tr_up: after: s2e0 = %a\n"
      fprint_sexp2 s2e0 in
*)
  let () = match d2e0.dexp2_type with
    | None -> ()
    | Some s2e ->
	let () = SOL.sexp2_tyleq_solve d2e0.dexp2_loc s2e0 s2e in
	  d3e0.dexp3_type <- s2e in
    d3e0

and dexp2_tr_up_main (d2e0: dexp2): dexp3 =
(*
  let () =
    P.fprintf stdout "dexp2_tr_up_main: d2e0 = %a\n"
      fprint_dexp2 d2e0 in
*)
  let loc0 = d2e0.dexp2_loc in match d2e0.dexp2_node with
    | DE2ann_type (d2e, s2e) -> begin
	let d3e = dexp2_tr_dn d2e s2e in let () = d3e.dexp3_type <- s2e in d3e
      end (* end of [DE2ann_type] *)
    | DE2ann_seff (d2e, sf2e) -> dexp2_tr_up d2e
    | DE2apps (d2e_fun, d2as) -> begin match d2e_fun.dexp2_node with
	| DE2mac d2m ->
	    if d2m.dmac2_abbrev then
	      dexp2_tr_up (Mac.macro_decode_abbrev loc0 d2m d2as)
	    else begin
	      P.eprintf
		"%a: long macro application needs to be decoded as such ,(...)\n"
		Loc.fprint loc0;
	      Err.abort ();
	    end
	| DE2sym d2s -> dexp2_apps_sym_tr_up loc0 d2s d2as
	| _ ->
	    let d3e_fun = dexp2_tr_up d2e_fun in
	    let () = dexp3_open_and_add d3e_fun in
	      dexp2_apps_tr_up loc0 d3e_fun d2as
      end (* end of [DE2apps] *)
    | DE2arr (s2e_elt, d2es_elt) -> dexp2_arr_tr_up loc0 s2e_elt d2es_elt
    | DE2arrsub (d2s_brackets, d2e_arr, d2ess_ind) ->
	dexp2_arrsub_tr_up loc0 d2s_brackets d2e_arr d2ess_ind
    | DE2assgn (d2e1, d2e2) -> dexp2_assgn_tr_up loc0 d2e1 d2e2
    | DE2case _ -> begin
	let s2e = SEnv3.sexp2_Var_new loc0 srt2_t0ype in
	  dexp2_tr_dn d2e0 s2e
      end (* end of [DE2case] *)
    | DE2char c -> dexp3_char loc0 c
    | DE2con (d2c, s2as, npf, d2es) ->
	dexp2_con_tr_up loc0 d2c s2as npf d2es
    | DE2cst d2c -> dexp2_cst_tr_up loc0 d2c
    | DE2crypt (knd, d2e) -> dexp2_crypt_tr_up loc0 knd d2e
    | DE2delay d2e -> dexp2_delay_tr_up loc0 d2e
    | DE2demac d2e -> begin
	let d2e = Mac.macro_decode d2e in
(*
	let () =
	  P.fprintf stdout
	    "dexp2_tr_up: DE2demac: d2e = %a\n" fprint_dexp2 d2e in
*)
	  dexp2_tr_up d2e
      end (* end of [DE2demac] *)
    | DE2deref d2e -> dexp2_deref_tr_up loc0 d2e []
    | DE2dynload filename -> dexp3_dynload loc0 filename
    | DE2effmask (eff, d2e) -> begin
	let () = SEnv3.effenv_push_with_effmask eff in
	let d3e = dexp2_tr_up d2e in
	let () = SEnv3.effenv_pop () in d3e
      end (* end of [DE2effmask] *)
    | DE2empty -> dexp3_empty loc0
    | DE2enmac _ -> begin
	error_with_loc loc0 "dexp2_tr_up_main: DE2enmac"
      end (* end of [DE2enmac] *)
    | DE2extval (s2e, code) -> dexp3_extval loc0 s2e code
    | DE2fix (d2v_fun, d2e_def) -> begin
	let s2e_master = type_of_dexp2 d2e_def in
	let () = d2v_fun.dvar2_master_type <- s2e_master in
	let s2e = SEnv3.sexp2_open_and_add s2e_master in
	let () = d2v_fun.dvar2_type <- Some s2e in
	let d3e_def = dexp2_tr_dn d2e_def s2e_master in
	  dexp3_fix loc0 d2v_fun d3e_def
      end (* end of [DE2fix] *)
    | DE2float f -> dexp3_float loc0 f
    | DE2fold (s2c, d2e) -> begin
	let stamps = SS.stamps_get () in
	let s2e = sexp2_cst_type loc0 stamps s2c in
	let d3e = dexp2_tr_dn d2e (sexp2_unfold loc0 s2e) in
	  dexp3_fold loc0 s2e d3e
      end (* end of [DE2fold] *)
    | DE2foldat (s2as, d2e_at) -> dexp2_foldat_tr_up loc0 s2as d2e_at
    | DE2freeat (s2as, d2e_at) -> dexp2_freeat_tr_up loc0 s2as d2e_at
    | DE2for _ -> begin
	P.eprintf "%a: dexp2_tr_up: DE2for is currently not supported."
	  Loc.fprint loc0;
	Err.abort ();
      end (* end of [DE2for] *)
(*
    // this treatment of a for-loop does not handle [continue] correctly
    | DE2for (oinv, (d2e_ini, d2e_test, d2e_post), d2e_body) ->
	let d3e_ini = dexp2_tr_dn d2e_ini (sexp2_void_t0ype ()) in
	let d2e_body_new =
	  dexp2_seq d2e_body.dexp2_loc [d2e_body; d2e_post] in
	let d3e_loop =
          dexp2_while_tr_up loc0 oinv d2e_test d2e_body_new in
	let s2e = sexp2_void_t0ype () in
	  dexp3_seq_with_type loc0 s2e [d3e_ini; d3e_loop]
*)
    | DE2if (_, _, _, od2e_else) -> begin
	let s2e = match od2e_else with
	  | Some _ -> SEnv3.sexp2_Var_new loc0 srt2_t0ype
	  | None -> sexp2_void_t0ype () in
	  dexp2_tr_dn d2e0 s2e  
      end (* end of [DE2if] *)
    | DE2int (ik, i) -> dexp3_int loc0 ik i
    | DE2lam_dyn (is_lin, (npf, p2ts), d2e) -> begin
	let () = SEnv3.env_push () in
(*
	let () = SEnv3.fprint_the_effenv_item_list stdout in
*)
	let (d2e, fc) = dexp2_funclo_of_dexp2 d2e in
	let (d2e, sf2e) = dexp2_seff2_of_dexp2 d2e in
	let () = SEnv3.effenv_push_with_lam sf2e in
(*
	let () = SEnv3.fprint_the_effenv_item_list stdout in
*)
	let () = DEnv3.env_push_lam is_lin in
	let () = DEnv3.lamloop_push_lam () in
	let () = List.iter DEnv3.pat2_dvs_add_local p2ts in
(*
	let () =
	  P.fprintf stdout "dexp2_tr_up_main: DE2lam_dyn: p2ts = %a\n"
	    fprint_pat2_list p2ts in
	let () =
	  P.fprintf stdout "dexp2_tr_up_main: DE2lam_dyn: d2e = %a\n"
	    fprint_dexp2 d2e in
*)
	let p3ts = pat2_arg_list_tr_up npf p2ts in
	let d3e = dexp2_tr_up d2e in
	let () = DEnv3.dynenv_final_check loc0 in
	let () = if is_lin then DEnv3.dynenv_final_check_llam loc0 in
	let () = DEnv3.lamloop_pop () in
	let () = DEnv3.env_pop_lam () in
	let () = SEnv3.effenv_pop () in
	let () = SEnv3.env_pop_and_add () in
	  dexp3_lam_dyn loc0 fc is_lin sf2e (npf, p3ts) d3e
      end (* end of [DE2lam_dyn] *)
    | DE2lam_met (r, s2es, d2e) -> begin
	let () = SEnv3.metric_check loc0 s2es in
	let () = Met.push !r s2es in
	let d3e = dexp2_tr_up d2e in
	let () = Met.pop () in d3e
      end (* end of [DE2lam_met] *)
    | DE2lam_sta (s2vs, s2ps, d2e) -> begin
	let () = SEnv3.env_push () in
	let () = SEnv3.svar_list_add s2vs in
	let () = SEnv3.hypo_prop_list_add s2ps in
	let d3e = dexp2_tr_up d2e in
	let () = SEnv3.env_pop_and_add () in
	  dexp3_lam_sta loc0 s2vs s2ps d3e
      end (* end of [DE2lam_sta] *)
    | DE2lam_sta_para (s2vs, s2ps, d2e) -> begin
	let () = SEnv3.env_push () in
	let () = SEnv3.svar_list_add s2vs in
	let () = SEnv3.hypo_prop_list_add s2ps in
	let d3e = dexp2_tr_up d2e in
	let () = SEnv3.env_pop_and_add () in
	  dexp3_lam_sta_para loc0 s2vs s2ps d3e
      end (* end of [DE2lam_sta_para] *)
    | DE2let (d2cs, d2e) -> begin
	let () = SEnv3.effenv_push () in
	let () = SEnv3.scst2_push () in
	let () = DEnv3.env_push_let () in
	let d3cs = dec2_list_tr d2cs in
	let d3e = dexp2_tr_up d2e in
	let () = DEnv3.dynenv_final_check loc0 in
	let () = DEnv3.env_pop_let () in
	let () = SEnv3.scst2_pop_and_unbind () in
	let () = SEnv3.effenv_pop () in
	  dexp3_let loc0 d3cs d3e
      end (* end of [DE2let] *)
    | DE2lst d2es -> begin
	let size = List.length d2es in
	let s2e_elt = SEnv3.sexp2_Var_new loc0 srt2_t0ype in
	let s2e_lst = sexp2_list_t0ype_int_type s2e_elt size in
	let d3es = List.map (function d2e -> dexp2_tr_dn d2e s2e_elt) d2es in
	  dexp3_lst loc0 s2e_lst d3es
      end (* end of [DE2lst] *)
    | DE2loopexn i -> begin
	let (sbis, sty_init, sty_exit, inv_met) = DEnv3.lamloop_exn loc0 in
	let () = (* continue: i = 1 / break : i = 0 *)
	  if i > 0 then DEnv3.state_check_with_before loc0 sty_init inv_met sbis
	  else DEnv3.state_check_with_before loc0 sty_exit None sbis in
	  dexp3_loopexn loc0 i
      end (* end of [DE2loopexn] *)
    | DE2ptrof d2e ->  dexp2_ptrof_tr_up loc0 d2e
    | DE2rec (is_flat, (npf, ld2es)) -> begin
	let ld3es =
	  List.map (function (l, d2e) -> (l, dexp2_tr_up d2e)) ld2es in
	let ls2es =
	  List.map (function (l, d3e) -> (l, d3e.dexp3_type)) ld3es in
	let k = tyrec_kind_of_flatness is_flat in
	let s2e = sexp2_tyrec k npf ls2es in
	  dexp3_rec loc0 s2e is_flat npf ld3es
      end (* end of [DE2rec] *)
    | DE2sel (d2e, ls) -> dexp2_sel_tr_up loc0 d2e ls
    | DE2seq d2es -> dexp2_seq_tr loc0 d2es None
    | DE2string s -> dexp3_string loc0 s
    | DE2template (d2e, s2ess0) -> begin
(*
	let () =
	  P.fprintf stdout "dexp2_tr_up_main: DE2template: s2ess0 = %a\n"
	    fprint_sexp2_list_list s2ess0 in
*)
	match d2e.dexp2_node with
	  | DE2cst d2c -> begin
	      let s2e_d2c = d2c.dcst2_type in
	      let (subs, s2e_tmp) =
		SEnv3.sexp2_template_inst loc0 s2ess0 d2c.dcst2_decarg s2e_d2c in
	      let s2ess =
		List.map (List.map (function (_, s2e) -> s2e)) subs in
		dexp3_template_cst loc0 s2e_tmp d2c s2ess
	    end
	  | DE2var d2v -> begin
	      let s2e_d2v = type_of_dvar2 loc0 d2v in
	      let (subs, s2e_tmp) =
		SEnv3.sexp2_template_inst loc0 s2ess0 d2v.dvar2_decarg s2e_d2v in
	      let s2ess =
		List.map (List.map (function (_, s2e) -> s2e)) subs in
		dexp3_template_var loc0 s2e_tmp d2v s2ess
	    end
	  | _ -> begin
	      P.eprintf "%a: ats_trans3: dexp2_tr_up_main: DE2template: d2e = %a\n"
		Loc.fprint loc0 fprint_dexp2 d2e;
	      Err.abort ()
	    end
      end
    | DE2top -> begin
	P.eprintf "%a: ats_trans3: dexp2_tr_up_main: DE2top: no type synthesis\n"
	  Loc.fprint loc0;
	Err.abort ()
      end (* end of [DE2top] *)
    | DE2trywith (d2e, c2ls) -> begin
	let () = DEnv3.env_push_try () in
	let d3e = dexp2_tr_up d2e in
	let s2e_exn = Exception_viewtype.make_exp None in
	let c3ls = (* no warning on exhaustiveness *)
	  cla2_list_tr loc0
	    (-1) (*sgn*) statype2_nil c2ls None [s2e_exn] d3e.dexp3_type in 
	let () = DEnv3.env_pop_try () in
	  dexp3_trywith loc0 d3e c3ls
      end (* end of [DE2trywith] *)
    | DE2unfold (s2c, d2e) -> begin
	let d3e = dexp2_tr_up d2e in
	let stamps = SS.stamps_get () in
	let s2e = sexp2_cst_type loc0 stamps s2c in
	let () = dexp3_tr_dn d3e s2e in
	  dexp3_unfold loc0 (sexp2_unfold loc0 s2e) d3e
      end (* end of [DE2unfold] *)
    | DE2var d2v -> dexp2_var_tr_up loc0 d2v
    | DE2viewat d2e -> dexp2_viewat_tr_up loc0 d2e
    | DE2while (oinv, d2e_test, d2e_body) ->
        dexp2_while_tr_up loc0 oinv d2e_test d2e_body
    | _ -> begin
	P.eprintf "%a: dexp2_tr_up: %a\n" Loc.fprint loc0 fprint_dexp2 d2e0;
	Err.abort ();
      end (* end of [_] *)
(* end of [dexp2_tr_up_main] *)

(* ****** ****** *)

and dexp2_arg_list_tr_up (d2es: dexp2 list): dexp23 list =
  let rec aux res = function
    | [] -> List.rev res
    | d2e :: d2es -> begin
	if dexp2_is_lamvar d2e then
	  aux (DE23dexp2 d2e :: res) d2es
	else let d3e = dexp2_tr_up d2e in
	  aux (DE23dexp3 d3e :: res) d2es
      end in
    aux [] d2es

and dexp23_arg_list_tr_up (d23es: dexp23 list): dexp3 list =
  let rec aux res = function
    | [] -> List.rev res
    | d23e :: d23es -> begin
	let d3e = match d23e with
	  | DE23dexp2 d2e -> dexp2_tr_up d2e
	  | DE23dexp3 d3e -> d3e in
	  aux (d3e :: res) d23es
      end in
    aux [] d23es

(* ****** ****** *)

and dexp2_list_tr_up (d2es: dexp2 list): dexp3 list =
  List.map dexp2_tr_up d2es

and dexp2_list_list_tr_up (d2ess: dexp2 list list): dexp3 list list =
  List.map dexp2_list_tr_up d2ess

and labdexp2_list_tr_up (ld2es: labdexp2 list): labdexp3 list =
  List.map (function (l, d2e) -> (l, dexp2_tr_up d2e)) ld2es

and dexp2_opt_tr_up (od2e: dexp2 option): dexp3 option =
  match od2e with Some d2e -> Some (dexp2_tr_up d2e) | None -> None

and dlab2_tr_up (d2lab: dlab2): dlab3_nt =
  let ind3 = match d2lab.dlab2_ind with
    | Some d2ess -> Some (dexp2_list_list_tr_up d2ess)
    | None -> None in
    dlab3_nt_olab_oind d2lab.dlab2_lab ind3

and dlab2_list_tr_up (d2labs: dlab2 list): dlab3_nt list =
  List.map dlab2_tr_up d2labs

(* ****** ****** *)

and dexp2_apps_tr_up loc0
  (d3e_fun: dexp3) (d2as: dexparg2 list): dexp3 = match d2as with
    | [] -> d3e_fun
    | d2a :: d2as -> begin match d2a with
	| DEXPARG2sta s2as ->
	    dexp2_apps_sta_tr_up loc0 d3e_fun s2as d2as
	| DEXPARG2dyn (npf, d2es) ->
	    dexp2_apps_dyn_tr_up loc0 d3e_fun npf d2es d2as
      end

and dexp2_apps_sta_tr_up loc0
  (d3e_fun: dexp3) (s2as: sexparg2 list) (d2as: dexparg2 list): dexp3 =
  let s2e_fun =
    let () = dexp3_open_and_add d3e_fun in 
      SEnv3.sexp2_uni_inst_sexparg2_list loc0 d3e_fun.dexp3_type s2as in
  let d3e_fun = dexp3_app_sta_with_type loc0 s2e_fun d3e_fun in
    dexp2_apps_tr_up loc0 d3e_fun d2as

and dexp2_apps_dyn_tr_up loc0
  (d3e_fun: dexp3) (npf: int) (d2es_arg: dexp2 list) (d2as: dexparg2 list)
  : dexp3 = 
  let s2e_fun =
    let () = dexp3_open_and_add d3e_fun in d3e_fun.dexp3_type in
    match s2e_fun.sexp2_node with
      | (SE2Var _  | SE2VarApp _) as sn ->
	  let d3es_arg = dexp2_list_tr_up d2es_arg in
	  let () = dexp3_list_open_and_add d3es_arg in
	  let s2es_arg = type_of_dexp3_list d3es_arg in
	  let s2e_res = match sn with
	    | SE2VarApp _ -> SEnv3.sexp2_VarApp_new loc0 srt2_t0ype
	    | _ (* SE2Var *) -> SEnv3.sexp2_Var_new loc0 srt2_t0ype in
	  let () =
	    let s2e_fun_new = 
	      sexp2_fun_with_sort srt2_type
		0(*lin*) seff2_all (npf, s2es_arg) s2e_res in
	    SOL.sexp2_tyleq_solve loc0 s2e_fun s2e_fun_new in
	  let () = SEnv3.effenv_check_all loc0 in
	  let d3e_app =
	    dexp3_app_dyn_with_type
	      loc0 s2e_res seff2_all d3e_fun (npf, d3es_arg) in
	    dexp2_apps_tr_up loc0 d3e_app d2as
      | _ -> begin
	  let d23es_arg = dexp2_arg_list_tr_up d2es_arg in
	  let () = dexp23_arg_list_open_and_add d23es_arg in
	  let d3e_app = dexp23_app_tr_up loc0 d3e_fun npf d23es_arg in
	    dexp2_apps_tr_up loc0 d3e_app d2as
	end

(* ****** ****** *)

and dexp23_app_tr_up loc0
  (d3e_fun: dexp3) (npf: int) (d23es_arg: dexp23 list): dexp3 = begin
  let s2e = d3e_fun.dexp3_type in
  let s2e_new = SEnv3.sexp2_uni_inst_all loc0 s2e in
  let () = d3e_fun.dexp3_type <- s2e_new in
  let s2e_fun = match s2e_new.sexp2_node with
    | SE2clo (_(*knd*), s2e_fun) -> s2e_fun | SE2fun _ -> s2e_new
    | _ -> begin
	P.eprintf "%a: dexp23_app_tr_up: not a function/closure type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e_new;
	Err.abort ()
      end in
    match s2e_fun.sexp2_node with
      | SE2fun (lin, sf2e_fun, (npf_fun, s2es_fun_arg), s2e_fun_res) ->
(*
	  let () =
	    P.fprintf stdout "dexp23_app_tr_up: sf2e_fun = %a\n"
	      fprint_seff2 sf2e_fun in
	  let () =
	    P.fprintf stdout "dexp23_app_tr_up: npf = %i and npf_fun = %i\n"
	      npf npf_fun in
*)
	  let () = SOL.pfarity_equal_solve loc0 npf npf_fun in
	  let d3e_fun_new = dexp3_restore_fun d3e_fun in
	  let d3es_arg =
	    let s2es = List.map un_sexp2_refarg_arg s2es_fun_arg in
	      dexp23_arg_list_tr_dn loc0 d23es_arg s2es in
          let d3es_arg_new = dexp3_list_restore_arg d3es_arg s2es_fun_arg in
	  let () = SEnv3.effenv_check_seff2 loc0 sf2e_fun in
	    dexp3_app_dyn_with_type loc0
	      s2e_fun_res sf2e_fun d3e_fun_new (npf, d3es_arg_new)
      | _ -> begin
	  error_of_deadcode "dexp23_app_tr_up: s2e_new: not a function type"
	end
end (* end of [dexp23_app_tr_up] *)

(* ****** ****** *)

and dexp2_apps_sym_tr_up loc0 (d2s: dsym2) (d2as: dexparg2 list): dexp3 =
  let f d2i =
    let d3e = dexp2_item_tr_up loc0 d2i in
    let sk = skexp2_of_sexp2 d3e.dexp3_type in
      (d3e, sk, []) in
  let xyzs = List.map f d2s.dsym2_item in
    dexp2_apps_sym_tr_up_aux1 loc0 d2s [] xyzs d2as

and dexp2_apps_sym_tr_up_aux1 loc0
  (d2s: dsym2) (d3as: dexparg3 list)
  (xyzs: (dexp3 * skexp2 * skexp2 list list) list)
  (d2as: dexparg2 list): dexp3 = match xyzs with
    | [] -> begin
	P.eprintf
	  "%a: dexp2_apps_sym_tr_up_aux1: the symbol <%a> is inapplicable.\n"
	  Loc.fprint loc0 fprint_dsym2 d2s;
	Err.abort ();
      end
    | [(d3e, _, _)] -> dexp2_apps_sym_tr_up_aux2 loc0 d3e (List.rev d3as) d2as
    | _ -> begin match d2as with
	| [] -> begin match ditem2_list_sort_args xyzs with
	    | [(d3e, _, _)] ->
		dexp2_apps_sym_tr_up_aux2 loc0 d3e (List.rev d3as) d2as
	    | xyzs -> begin
		P.eprintf
		  "%a: dexp2_apps_sym_tr_up_aux1: the symbol <%a> cannot be resolved: %a.\n"
		  Loc.fprint loc0 fprint_dsym2 d2s fprint_ditem2_xyzs xyzs;
		Err.abort ();
	      end
	  end
	| d2a :: d2as -> begin match d2a with
	    | DEXPARG2sta s2as ->
		let d3a = DEXPARG3sta s2as in
		  dexp2_apps_sym_tr_up_aux1 loc0 d2s (d3a :: d3as) xyzs d2as
	    | DEXPARG2dyn (npf, d2es) ->
		let d3es = dexp23_arg_list_tr_up (dexp2_arg_list_tr_up d2es) in
(*
		let () =
		  P.fprintf stdout "dexp2_apps_sym_tr_up_aux1: s2es = %a\n"
		    fprint_sexp2_list (type_of_dexp3_list d3es) in
*)
		let d3a = DEXPARG3dyn (npf, d3es) in
		let sks = List.map skexp2_of_dexp3 d3es in
		let xyzs = ditem2_list_select_args sks xyzs in
		  dexp2_apps_sym_tr_up_aux1 loc0 d2s (d3a :: d3as) xyzs d2as
	  end
      end

and dexp2_apps_sym_tr_up_aux2 loc0
  (d3e: dexp3) (d3as: dexparg3 list) (d2as: dexparg2 list): dexp3 =
  let rec aux d3e_fun d3as = match d3as with
    | [] -> dexp2_apps_tr_up loc0 d3e_fun d2as
    | DEXPARG3sta s2as :: d3as ->
	let s2e_fun =
	  SEnv3.sexp2_uni_inst_sexparg2_list loc0 d3e_fun.dexp3_type s2as in
	let d3e_fun = dexp3_app_sta_with_type loc0 s2e_fun d3e_fun in
	  aux d3e_fun d3as
    | DEXPARG3dyn (npf, d3es_arg) :: d3as ->
	let () = dexp3_list_open_and_add d3es_arg in
	let s2es_arg = type_of_dexp3_list d3es_arg in
	let s2e_fun = SEnv3.sexp2_uni_inst_all loc0 d3e_fun.dexp3_type in
	let () = d3e_fun.dexp3_type <- s2e_fun in
	  begin match s2e_fun.sexp2_node with
	    | SE2fun (lin, sf2e_fun, (npf_fun, s2es_fun_arg), s2e_fun_res) ->
		let () = SOL.pfarity_equal_solve loc0 npf npf_fun in
		let d3e_fun_new = dexp3_restore_fun d3e_fun in
		let () =
		  let s2es = List.map un_sexp2_refarg_arg s2es_fun_arg in
		    SOL.sexp2_list_tyleq_solve loc0 s2es_arg s2es in
                let d3es_arg_new = dexp3_list_restore_arg d3es_arg s2es_fun_arg in
		let () = SEnv3.effenv_check_seff2 loc0 sf2e_fun in
		let d3e_app =
		  dexp3_app_dyn_with_type loc0
		    s2e_fun_res sf2e_fun d3e_fun_new (npf, d3es_arg_new) in
		  aux d3e_app d3as
	    | _ -> begin
		P.eprintf
		  "%a: dexp2_apps_sym_tr_up_aux2: not a function type: %a\n"
		  Loc.fprint loc0 fprint_sexp2 s2e_fun;
		Err.abort ();
	      end
	  end in
    aux d3e d3as

(* ****** ****** *)

and dexp2_arr_tr_up loc0
  (s2e_elt: sexp2) (d2es_elt: dexp2 list): dexp3 =
  let n = List.length d2es_elt in
  let d3es_elt =
    List.map (function d2e -> dexp2_tr_dn d2e s2e_elt) d2es_elt in
  let s2e_arr = sexp2_arrayptrsize_viewt0ype_int_viewt0ype s2e_elt n in
    dexp3_arr_with_type loc0 s2e_arr s2e_elt d3es_elt

and dexp2_arrsub_tr_up loc0
  (d2s_brackets: dsym2) (d2e_arr: dexp2) (d2ess_ind: dexp2 list list): dexp3 =
  if dexp2_var_is_ptr d2e_arr then
    dexp2_deref_tr_up loc0 d2e_arr [dlab2_ind d2ess_ind]
  else begin match d2ess_ind with
    | [d2es_ind] ->
	let d2a = DEXPARG2dyn (0, d2e_arr :: d2es_ind) in
	  dexp2_apps_sym_tr_up loc0 d2s_brackets [d2a]
    | _ -> begin
	P.eprintf
          "%a: dexp2_arrsub_tr_up: the index format is not supported.\n"
	  Loc.fprint loc0;
	Err.abort ();
      end
  end
	  
(* ****** ****** *)

and dexp2_assgn_tr_up loc0 (d2e1: dexp2) (d2e2: dexp2): dexp3 =
  let l2v1 = lval2_of_dexp2 d2e1 in match l2v1 with
    | LVAL2arrsub (d2s_brackets, d2e1_arr, d2ess1_ind) -> begin
	match d2ess1_ind with
	  | [d2es1_ind] ->
	      let d2a = DEXPARG2dyn (0, d2e1_arr :: (d2es1_ind @ [d2e2])) in
		dexp2_apps_sym_tr_up loc0 d2s_brackets [d2a]
	  | _ -> begin
	      P.eprintf
		"%a: dexp2_assgn_tr_up: DE2arrsub: not supported index format.\n"
		Loc.fprint loc0;
	      Err.abort ();
	    end
      end

    | LVAL2ptr (d2e1, []) -> begin
	let d3e1 = dexp2_tr_up d2e1 in
	let () = dexp3_open_and_add d3e1 in
	let s2e1 = d3e1.dexp3_type in
	  match un_sexp2_ptr_addr_type s2e1 with
	    | Some s2l1 ->
		let d3e2 = dexp2_tr_up d2e2 in
		let () = dexp3_open_and_add d3e2 in
		let s2e2 = d3e2.dexp3_type in
		let _ (* s2labs *) = addr_assgn_sel loc0 s2l1 [] s2e2 in
		  dexp3_assgn_ptr loc0 d3e1 [] d3e2
	    | None -> begin match un_sexp2_ref_viewt0ype_type s2e1 with
		| Some s2e1_elt ->
                    let () = SEnv3.effenv_check_ref loc0 in (* reference write *)
		    let () =
		      if sexp2_is_linear s2e1_elt then
			assgn_lintype_discard_errmsg loc0 s2e1_elt in
		    let d3e2 = dexp2_tr_dn d2e2 s2e1_elt in
		      dexp3_assgn_ptr loc0 d3e1 [] d3e2
		| None -> begin
		    P.eprintf "%a: dexp2_assgn_tr_up: not a pointer or reference.\n"
		      Loc.fprint d2e1.dexp2_loc;
		    Err.abort ();
		  end
	      end
      end

    | LVAL2ptr (d2e1, d2labs) -> begin
	let d3e1 = dexp2_tr_up d2e1 in
	let () = dexp3_open_and_add d3e1 in
	let s2e1 = d3e1.dexp3_type in
	  match un_sexp2_ptr_addr_type s2e1 with
	    | Some s2l1 ->
		let d3labs_nt = dlab2_list_tr_up d2labs in
		let s2labs_nt = slab2_of_dlab3_nt_list d3labs_nt in
		let d3e2 = dexp2_tr_up d2e2 in
		let () = dexp3_open_and_add d3e2 in
		let s2e2 = d3e2.dexp3_type in
		let s2labs = addr_assgn_sel loc0 s2l1 s2labs_nt s2e2 in
		let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
		  dexp3_assgn_ptr loc0 d3e1 d3labs d3e2
	    | None -> begin
		P.eprintf "%a: dexp2_assgn_tr_up: LVAL2ptr: not a pointer.\n"
		  Loc.fprint d2e1.dexp2_loc;
		Err.abort ();
	      end
      end

    | LVAL2var_lin (d2v1, d2labs) ->
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let d3e2 = dexp2_tr_up d2e2 in
	let () = dexp3_open_and_add d3e2 in
	let s2e2 = d3e2.dexp3_type in
	let () = (* [d3e2] needs to be a proof *)
	  if sexp2_is_proof s2e2 then () else begin
	    P.eprintf "%a: dexp2_assgn_tr_up: LVAL2val_lin: not a proof.\n"
	      Loc.fprint d2e1.dexp2_loc;
	    Err.abort ();
	  end in
	let s2labs = dvar2_lin_assgn_sel loc0 d2v1 s2labs s2e2 in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	  dexp3_assgn_var loc0 d2v1 d3labs d3e2

    | LVAL2var_mut (d2v1, d2labs) ->
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let d3e2 = dexp2_tr_up d2e2 in
	let () = dexp3_open_and_add d3e2 in
	let s2labs = dvar2_mut_assgn_sel loc0 d2v1 s2labs d3e2.dexp3_type in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	  dexp3_assgn_var loc0 d2v1 d3labs d3e2

    | LVAL2none d2e1 -> begin match d2e1.dexp2_node with
	| DE2viewat d2e1 -> dexp2_viewat_assgn_tr_up loc0 d2e1 d2e2
	| _ -> begin
	    P.eprintf "%a: dexp2_assgn_tr_up: not a left value: <%a>\n"
	      Loc.fprint loc0 fprint_dexp2 d2e1;
	    Err.abort ()
	  end
      end

and dexp2_viewat_assgn_tr_up loc0 (d2e1: dexp2) (d2e2: dexp2): dexp3 =
  let l2v1 = lval2_of_dexp2 d2e1 in match l2v1 with
    | LVAL2ptr (d2e1, d2labs) -> begin
	let d3e1 = dexp2_tr_up d2e1 in
	let () = dexp3_open_and_add d3e1 in
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let d3e2 = dexp2_tr_up d2e2 in
	let () = dexp3_open_and_add d3e2 in
	let s2e1 = d3e1.dexp3_type and s2e2 = d3e2.dexp3_type in
	  match un_sexp2_ptr_addr_type s2e1 with
	    | Some s2l1 ->
		let s2labs = addr_viewat_set loc0 s2l1 s2labs s2e2 in
		let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
		  dexp3_viewat_assgn_ptr loc0 d3e1 d3labs d3e2
	    | None -> begin
		P.eprintf "%a: dexp2_viewat_assgn_tr_up: not a pointer.\n"
		  Loc.fprint d2e1.dexp2_loc;
		Err.abort ();
	      end
      end
    | LVAL2var_mut (d2v1, []) ->
	let d3e2 = dexp2_tr_up d2e2 in
	let () = dexp3_open_and_add d3e2 in
	let d2v1_view = dvar2_view_of_dvar2 d2v1 in
	let () = match d2v1_view.dvar2_type with
	  | Some s2e1 -> SOL.sexp2_void_solve loc0 s2e1 | None -> () in
	let () = dvar2_set_type d2v1_view d3e2.dexp3_type in
	  dexp3_viewat_assgn_var loc0 d2v1 [] d3e2
    | LVAL2var_mut (d2v1, d2labs) ->
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let d3e2 = dexp2_tr_up d2e2 in
	let () = dexp3_open_and_add d3e2 in
	let s2labs =
	  dvar2_mut_viewat_set loc0 d2v1 s2labs d3e2.dexp3_type in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	  dexp3_viewat_assgn_var loc0 d2v1 d3labs d3e2

    | LVAL2arrsub _ -> begin
	P.eprintf
	  "%a: dexp2_viewat_assgn_tr_up: array subscripting is not supported.\n"
	  Loc.fprint loc0;
	  Err.abort ();
      end
    | LVAL2var_lin (d2v, d2labs) -> begin
	P.eprintf
	  "%a: dexp2_viewat_assgn_tr_up: linear variable is not supported: <%a>.\n"
	  Loc.fprint loc0 fprint_dvar2 d2v;
	Err.abort ();
      end 
    | LVAL2none d2e -> begin
	P.eprintf "%a: dexp2_viewat_assgn_tr_up: not a left value: <%a>.\n"
	  Loc.fprint loc0 fprint_dexp2 d2e;
	Err.abort ();	  
      end

(* ****** ****** *)

and dexp2_con_tr_up loc0 (d2c: dcon2)
  (s2as: sexparg2 list) (npf: int) (d2es_arg: dexp2 list): dexp3 =
  let d23es_arg = dexp2_arg_list_tr_up d2es_arg in
  let () = dexp23_arg_list_open_and_add d23es_arg in
  let s2e = SEnv3.sexp2_uni_inst_sexparg2_list loc0 d2c.dcon2_type s2as in
  let s2e = SEnv3.sexp2_uni_inst_all loc0 s2e in match s2e.sexp2_node with
    | SE2fun (
	_(*lin*), _(*sf2e*), (npf_fun, s2es_fun_arg), s2e_fun_res
      ) -> begin
	let () = SOL.pfarity_equal_solve loc0 npf npf_fun in
	let d3es_arg = dexp23_arg_list_tr_dn loc0 d23es_arg s2es_fun_arg in
	  dexp3_con loc0 s2e_fun_res d2c (npf, d3es_arg)
      end
    | _ -> begin
	P.eprintf "%a: dexp2_con_tr_up: not a function type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end

(* ****** ****** *)

and dexp2_cst_tr_up loc0 (d2c: dcst2): dexp3 =
  let s2e_d2c = d2c.dcst2_type in
    match d2c.dcst2_decarg with
      | [] -> dexp3_cst loc0 d2c
      | s2vpss -> begin
	  let (subs, s2e_tmp) =
	    SEnv3.sexp2_template_inst loc0 [] s2vpss s2e_d2c in
	  let s2ess =
	    List.map (List.map (function (_, s2e) -> s2e)) subs in
	    dexp3_template_cst loc0 s2e_tmp d2c s2ess
	end

(* ****** ****** *)

and dexp2_crypt_tr_up loc0 (knd: int) (d2e: dexp2): dexp3 =
  if knd > 0 then begin
    dexp2_encrypt_tr_up loc0 d2e
  end else begin
    dexp2_decrypt_tr_up loc0 d2e
  end

and dexp2_encrypt_tr_up loc0 (d2e: dexp2): dexp3 =
  let d3e = dexp2_tr_up d2e in
  let s2e = sexp2_crypt_viewt0ype_viewt0ype d3e.dexp3_type in
    dexp3_crypt loc0 s2e 1(*encrypt*) d3e

and dexp2_decrypt_tr_up loc0 (d2e: dexp2): dexp3 =
  let d3e = dexp2_tr_up d2e in
  let s2e_crypt = d3e.dexp3_type in
  let s2e = match
    un_sexp2_crypt_viewt0ype_viewt0ype s2e_crypt with
    | Some s2e -> s2e
    | None -> begin
        P.eprintf
          "%a: dexp2_decrypt_tr_up: not a crypt type: <%a>\n"
          Loc.fprint loc0 fprint_sexp2 s2e_crypt;
        Err.abort ()
      end in
    dexp3_crypt loc0 s2e (-1)(*decrypt*) d3e

(* ****** ****** *)

and dexp2_delay_tr_up loc0 (d2e: dexp2): dexp3 =
  let () = SEnv3.env_push () in
  let () = SEnv3.effenv_push_with_lam seff2_all in
  let () = DEnv3.env_push_lam true(*lin*) in
  let () = DEnv3.lamloop_push_lam () in
  let d3e = dexp2_tr_up d2e in
  let () = DEnv3.dynenv_final_check loc0 in
  let () = DEnv3.dynenv_final_check_llam loc0 in
  let () = DEnv3.lamloop_pop () in
  let () = DEnv3.env_pop_lam () in
  let () = SEnv3.effenv_pop () in
  let () = SEnv3.env_pop_and_add () in
  let s2e = d3e.dexp3_type in
  let lin = if sexp2_is_linear s2e then 1 else 0 in
  let s2e_lazy =
    if lin > 0 then begin
      sexp2_lazy_viewt0ype_viewtype (s2e)
    end else begin
      sexp2_lazy_t0ype_type (s2e)
    end in
    dexp3_delay loc0 s2e_lazy lin d3e

(* ****** ****** *)

and dexp2_deref_tr_up loc0 (d2e_ptr: dexp2) (d2labs: dlab2 list): dexp3 =
(*
  let () =
    P.fprintf stdout "dexp2_deref_tr_up: d2e0 = %a\n" fprint_dexp2 d2e0 in
*)
  let d3e_ptr = dexp2_tr_up d2e_ptr in
  let s2e_ptr =
    let () = dexp3_open_and_add d3e_ptr in d3e_ptr.dexp3_type in
(*
  let () =
    P.fprintf stdout "dexp2_deref_tr_up: s2e_ptr = %a\n" fprint_sexp2 s2e_ptr in
*)
    begin match d2labs with
      | [] -> begin match un_sexp2_ptr_addr_type s2e_ptr with
	  | Some s2l ->
	      let (s2e, _ (* s2labs *)) = addr_deref_sel loc0 s2l [] in
(*
   	      let () =
		P.fprintf stdout "dexp2_deref_tr_up: s2e = %a\n" fprint_sexp2 s2e in
*)
		dexp3_sel_ptr loc0 s2e d3e_ptr []
	  | None -> begin match un_sexp2_ref_viewt0ype_type s2e_ptr with
	      | Some s2e_elt ->
                  let () = SEnv3.effenv_check_ref loc0 in (* reference read *)
		  let () =
		    if sexp2_is_linear s2e_elt then
		      deref_lintype_duplicate_errmsg loc0 s2e_elt in
		    dexp3_sel_ptr loc0 s2e_elt d3e_ptr []
	      | None -> begin match un_sexp2_refconst_t0ype_type s2e_ptr with
		  | Some s2e_elt ->  dexp3_sel_ptr loc0 s2e_elt d3e_ptr []
		  | None -> begin
		      P.eprintf
			"%a: dexp2_deref_tr_up: not a pointer or reference type: <%a>\n"
			Loc.fprint loc0 fprint_sexp2 s2e_ptr;
		      Err.abort ()
		    end
		end
	    end
	end
      | _ :: _ -> begin
	  match un_sexp2_ptr_addr_type s2e_ptr with
	    | Some s2l ->
		let d3labs_nt = dlab2_list_tr_up d2labs in
		let s2labs_nt = slab2_of_dlab3_nt_list d3labs_nt in
		let (s2e, s2labs) = addr_deref_sel loc0 s2l s2labs_nt in
		let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
(*
		let () =
		  P.fprintf stdout "dexp2_deref_tr_up: s2e = %a\n" fprint_sexp2 s2e in
*)
		  dexp3_sel_ptr loc0 s2e d3e_ptr d3labs
	    | None -> begin
		P.eprintf "%a: dexp2_deref_tr_up: not a pointer type: <%a>\n"
		  Loc.fprint loc0 fprint_sexp2 s2e_ptr;
		Err.abort ()
	      end
	end
  end (* end of match *)

(* ****** ****** *)

and dexp2_foldat_tr_up loc0 (s2as: sexparg2 list) (d2e_at: dexp2): dexp3 =
  let aux_ptr (s2l: sexp2): sexp2 =
    match DEnv3.dvar2_viewat_find s2l [] with
      | Some (d2v_view, s2e_elt, s2l, s2labs_ft, s2labs_bk) ->
	  let () = d2v_view.dvar2_type <- None in s2e_elt
      | None -> error_of_deadcode "ats_trans3: dexp2_foldat_tr_up" in
  let d3e_at = dexp2_tr_up d2e_at in
  let s2e_at = d3e_at.dexp3_type in
  let (d2c, s2ls_arg) = match s2e_at.sexp2_node with
    | SE2datcon (d2c, s2ls) -> (d2c, s2ls)
    | _ -> begin
	P.eprintf "%a: dexp2_foldat_tr_up: expression cannot be folded: <%a>.\n"
	  Loc.fprint loc0 fprint_sexp2 s2e_at;
	Err.abort ();
      end in
  let s2es_arg = List.map aux_ptr s2ls_arg in
  let s2e = SEnv3.sexp2_uni_inst_sexparg2_list loc0 d2c.dcon2_type s2as in
  let s2e = SEnv3.sexp2_uni_inst_all loc0 s2e in
  let s2e_res = match s2e.sexp2_node with
    | SE2fun (_(*lin*), _(*sf2e*), (npf_fun, s2es_fun_arg), s2e_fun_res) ->
	let () = SOL.sexp2_list_tyleq_solve loc0 s2es_arg s2es_fun_arg in
	  s2e_fun_res
    | _ -> begin
	P.eprintf "%a: dexp2_foldat_tr_up: not a function type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end in
  let err = dexp3_lval_type_update loc0 0(*refval*) d3e_at s2e_res in
  let () =
    if err > 0 then begin
      P.eprintf "%a: the dynamic expression needs to be a left value for folding.\n"
	Loc.fprint loc0;
      Err.abort ()
    end in
    dexp3_foldat loc0 d3e_at

(* ****** ****** *)

and dexp2_freeat_tr_up loc0 (s2as: sexparg2 list) (d2e_at: dexp2): dexp3 =
  let aux_ptr (s2l: sexp2): sexp2 =
    match DEnv3.dvar2_viewat_find s2l [] with
      | Some (d2v_view, s2e_elt, s2l, s2labs_ft, s2labs_bk) ->
	  let () = d2v_view.dvar2_type <- None in s2e_elt
      | None -> error_of_deadcode "ats_trans3: dexp2_freeat_tr_up" in
  let d3e_at = dexp2_tr_up d2e_at in
  let s2e_at = d3e_at.dexp3_type in
  let (d2c, s2ls_arg) = match s2e_at.sexp2_node with
    | SE2datcon (d2c, s2ls) -> (d2c, s2ls)
    | _ -> begin
	P.eprintf "%a: dexp2_freeat_tr_up: expression cannot be freed: <%a>.\n"
	  Loc.fprint loc0 fprint_sexp2 s2e_at;
	Err.abort ();
      end in
  let s2es_arg = List.map aux_ptr s2ls_arg in
  let s2e = SEnv3.sexp2_uni_inst_sexparg2_list loc0 d2c.dcon2_type s2as in
  let s2e = SEnv3.sexp2_uni_inst_all loc0 s2e in
  let () = match s2e.sexp2_node with
    | SE2fun (_(*lin*), _(*sf2e*), (npf_fun, s2es_fun_arg), s2e_fun_res) ->
	let s2es_fun_arg = List.map sexp2_top s2es_fun_arg in
	  SOL.sexp2_list_tyleq_solve loc0 s2es_arg s2es_fun_arg
    | _ -> begin
	P.eprintf "%a: dexp2_freeat_tr_up: not a function type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end in
    dexp3_freeat loc0 d3e_at

(* ****** ****** *)

and dexp2_item_tr_up loc0 (d2i: ditem2): dexp3 =
  match d2i with
    | DI2cst d2c -> dexp2_cst_tr_up loc0 d2c
    | DI2var d2v -> dexp2_var_tr_up loc0 d2v
    | _ -> begin P.eprintf
	"%a: dexp2_item_tr_up: the item is required to be a constant or variable: <%a>.\n"
	Loc.fprint loc0 fprint_ditem2 d2i;
	Err.abort ();	
      end (* end of [_] *)
(* end of [dexp2_item_tr_up] *)

(* ****** ****** *)

and dexp2_ptrof_tr_up loc0 (d2e0: dexp2): dexp3 =
  let l2v = lval2_of_dexp2 d2e0 in match l2v with
    | LVAL2ptr (d2e_ptr, []) -> begin
	let d3e_ptr = dexp2_tr_up d2e_ptr in
	let () = dexp3_open_and_add d3e_ptr in
	let s2e_ptr = d3e_ptr.dexp3_type in
	let s2e = match un_sexp2_ptr_addr_type s2e_ptr with
	  | Some s2l -> Ptr_addr_type.make_exp (Some [s2l])
	  | None -> begin
	      P.eprintf "%a: dexp2_ptrof_tr_up: no a pointer type: <%a>.\n"
		Loc.fprint loc0 fprint_sexp2 s2e_ptr;
	      Err.abort ();
	    end in
	  dexp3_ptrof_ptr loc0 s2e d3e_ptr []
      end
    | LVAL2ptr (d2e_ptr, d2labs) -> begin
	let d3e_ptr = dexp2_tr_up d2e_ptr in
	let () = dexp3_open_and_add d3e_ptr in
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let s2e_ptr = d3e_ptr.dexp3_type in
	let (s2e, s2labs) = match un_sexp2_ptr_addr_type s2e_ptr with
	  | Some s2l ->
	      let s2labs = addr_probe_sel loc0 s2l s2labs in
	      let s2e =
		Ptr_addr_type.make_exp (Some [sexp2_proj_list s2l s2labs]) in
		(s2e, s2labs)
	  | None -> begin
	      P.eprintf "%a: dexp2_ptrof_tr_up: no a pointer type: <%a>.\n"
		Loc.fprint loc0 fprint_sexp2 s2e_ptr;
	      Err.abort ();
	    end in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	  dexp3_ptrof_ptr loc0 s2e d3e_ptr d3labs
      end
    | LVAL2var_mut (d2v, []) -> begin
	let s2l = addr_of_dvar2 d2v in
	let s2e = Ptr_addr_type.make_exp (Some [s2l]) in
	  dexp3_ptrof_var loc0 s2e d2v []
      end
    | LVAL2var_mut (d2v, d2labs) -> begin
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let s2labs = dvar2_mut_probe_sel loc0 d2v s2labs in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	let s2l = addr_of_dvar2 d2v in
	let s2e =
	  Ptr_addr_type.make_exp (Some [sexp2_proj_list s2l s2labs]) in
	  dexp3_ptrof_var loc0 s2e d2v d3labs
      end
    | LVAL2arrsub _ -> begin
	P.eprintf "%a: dexp2_ptrof_tr_up: array subscription.\n"
	  Loc.fprint loc0;
	Err.abort ();
      end
    | LVAL2var_lin (d2v, ls) -> begin
	P.eprintf "%a: dexp2_ptrof_tr_up: not a mutable variable: <%a>.\n"
	  Loc.fprint loc0 fprint_dvar2 d2v;
	Err.abort ();
      end 
    | LVAL2none d2e -> begin
	P.eprintf "%a: dexp2_ptrof_tr_up: not a left value: <%a>.\n"
	  Loc.fprint loc0 fprint_dexp2 d2e;
	Err.abort ();	  
      end

(* ****** ****** *)

and dexp2_sel_tr_up loc0 (d2e0: dexp2) (d2labs: dlab2 list): dexp3 =
(*
  let () =
    P.fprintf stdout "dexp2_sel_tr_up: d2e0 = %a\n" fprint_dexp2 d2e0 in
  let () = begin match d2e0.dexp2_node with
    | DE2var d2v -> begin
	P.fprintf stdout "dexp2_sel_tr_up: d2v = %a\n" fprint_dvar2 d2v;
	P.fprintf stdout "dexp2_sel_tr_up: d2v.lin = %i\n" d2v.dvar2_linear;
	P.fprintf stdout "dexp2_sel_tr_up: d2v.islin = %b\n" (dvar2_is_linear d2v);
      end
    | _ -> ()
  end in
*)
  match d2e0.dexp2_node with
    | DE2var d2v when dvar2_is_mutable d2v ->
(*
	let () =
	  P.fprintf stdout
	    "dexp2_sel_tr_up: mutable: d2v = %a\n" fprint_dvar2 d2v in
*)
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let (s2e, s2labs) = dvar2_mut_deref_sel loc0 d2v s2labs in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	  dexp3_sel_var loc0 s2e d2v d3labs
    | DE2var d2v when dvar2_is_linear d2v ->
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let (s2e_var, s2e, s2ps, s2labs) =
	  sexp2_select_list_get loc0 (type_of_dvar2 loc0 d2v) s2labs in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	let () = SEnv3.prop_list_add loc0 s2ps in
	let () = if sexp2_is_linear s2e then dvar2_set_type d2v s2e_var in
	  dexp3_sel_var loc0 s2e d2v d3labs
    | DE2deref d2e -> dexp2_deref_tr_up loc0 d2e d2labs
    | _ -> begin
	let d3e0 = dexp2_tr_up d2e0 in
	let d3labs_nt = dlab2_list_tr_up d2labs in
	  dexp3_sel_tr_up loc0 d3e0 d3labs_nt
      end

(* ****** ****** *)

and dexp2_var_tr_up loc0 d2v: dexp3 =
  let s2e_d2v = 
    if dvar2_is_mutable d2v then
      let (s2e, _) = dvar2_mut_deref_sel loc0 d2v [] in s2e
    else begin
      let s2e = type_of_dvar2 loc0 d2v in
      let () =
	if dvar2_is_linear d2v then
	  let is_local_llam = DEnv3.dvar2_is_local_llam d2v in
	    if is_local_llam then
	      begin
		d2v.dvar2_linear <- d2v.dvar2_linear + 1;
		d2v.dvar2_type <- None;
	      end
	    else dvar2_nonlocal_errmsg loc0 d2v
	else () in
	s2e
    end in
    begin match d2v.dvar2_decarg with
      | [] -> dexp3_var_with_type loc0 s2e_d2v d2v
      | s2vpss -> begin
	  let (subs, s2e_tmp) =
	    SEnv3.sexp2_template_inst loc0 [] s2vpss s2e_d2v in
	  let s2ess =
	    List.map (List.map (function (_, s2e) -> s2e)) subs in
	    dexp3_template_var loc0 s2e_tmp d2v s2ess
	end
    end

(* ****** ****** *)

and dexp2_viewat_tr_up loc0 (d2e0: dexp2): dexp3 =
  let l2v0 = lval2_of_dexp2 d2e0 in match l2v0 with
    | LVAL2ptr (d2e_ptr, d2labs) -> begin
	let d3e_ptr = dexp2_tr_up d2e_ptr in
	let () = dexp3_open_and_add d3e_ptr in
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let s2e_ptr = d3e_ptr.dexp3_type in
	  match un_sexp2_ptr_addr_type s2e_ptr with
	    | Some s2l ->
		let (s2e_at, s2labs, d2v_view, s2labs_view) =
		  addr_viewat_get loc0 s2l s2labs in
		let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
		  dexp3_viewat_ptr loc0 s2e_at d3e_ptr d3labs d2v_view s2labs_view
	    | None -> begin
		P.eprintf "%a: dexp2_viewat_assgn_tr_up: not a pointer.\n"
		  Loc.fprint d2e_ptr.dexp2_loc;
		Err.abort ();
	      end
      end
    | LVAL2var_mut (d2v, d2labs) ->
	let d3labs_nt = dlab2_list_tr_up d2labs in
	let s2labs = slab2_of_dlab3_nt_list d3labs_nt in
	let (s2e_at, s2labs, d2v_view, s2labs_view) =
	  dvar2_mut_viewat_get loc0 d2v s2labs in
	let d3labs = dlab3_of_dlab3_nt_slab2_list d3labs_nt s2labs in
	  dexp3_viewat_var loc0 s2e_at d2v d3labs d2v_view s2labs_view
    | LVAL2arrsub _ -> begin
	P.eprintf
	  "%a: dexp2_viewat_tr_up: array subscripting is not supported.\n"
	  Loc.fprint loc0;
	  Err.abort ();
      end
    | LVAL2var_lin (d2v, ls) -> begin
	P.eprintf
	  "%a: dexp2_viewat_tr_up: not a mutable variable: <%a>.\n"
	  Loc.fprint loc0 fprint_dvar2 d2v;
	Err.abort ();
      end 
    | LVAL2none d2e -> begin
	P.eprintf "%a: dexp2_viewat_tr_up: not a left value: <%a>.\n"
	  Loc.fprint loc0 fprint_dexp2 d2e;
	Err.abort ();	  
      end

(* ****** ****** *)

and dexp2_while_tr_up loc0
  (oinv: loopinv2 option) (d2e_test: dexp2) (d2e_body: dexp2): dexp3 =
  let inv = match oinv with
    | Some inv -> (* while* *)
	loopinv2_new inv
    | None -> (* while *)
	let arg = DEnv3.statype2_body_save () in
	  loopinv2_make loc0 [] [] None arg None in
  let sty_init =
    statype2_make
      inv.loopinv2_svs inv.loopinv2_gua inv.loopinv2_met inv.loopinv2_arg in
  let () = dexp2_while_tr_up_init inv in
  let (inv_met, sty_exit) = dexp2_while_tr_up_start inv in
  let sbis = DEnv3.state_before_save () in
  let () = DEnv3.lamloop_push_loop sbis sty_init sty_exit inv_met in
  let d3e_test =
    let d3e_test = dexp2_tr_up d2e_test in
    let () = dexp3_open_and_add d3e_test in
      d3e_test in
  let s2e_test = d3e_test.dexp3_type in
  let () = (* loop exit *)
    let () = SEnv3.env_push () in
    let _ = pat2_bool_tr_dn loc0 false s2e_test in
(*
    let () = P.fprintf stdout "dexp2_while_tr_up: state_check:\n" in
*)
    let () = DEnv3.state_check_with_before loc0 sty_exit None sbis in
    let () = SEnv3.env_pop_and_add () in () in
  let d3e_body = (* loop enter *)
    let () = SEnv3.env_push () in
    let _ = pat2_bool_tr_dn loc0 true s2e_test in
    let d3e_body = dexp2_tr_dn d2e_body (sexp2_void_t0ype ()) in
(*
    let () = P.fprintf stdout "dexp2_while_tr_up: state_check:\n" in
*)
    let () =
      if not (dexp2_is_raised d2e_body) then
	DEnv3.state_check_with_before loc0 sty_init inv_met sbis in
    let () = SEnv3.env_pop_and_add () in d3e_body in
  let () = DEnv3.state_update_with_before loc0 sty_exit sbis in
  let () = DEnv3.lamloop_pop () in
    dexp3_while loc0 d3e_test d3e_body

and dexp2_while_tr_up_init (inv: loopinv2): unit =
  let loc = inv.loopinv2_loc in
  let sub =
    SEnv3.sexp2_inst_and_add loc inv.loopinv2_svs inv.loopinv2_gua in
  let rec aux (d2v, os2e0) = match d2v.dvar2_type, os2e0 with
    | None, None -> ()
    | Some s2e, Some s2e0 ->
	SOL.sexp2_tyleq_solve loc s2e (sexp2_subst sub s2e0)
    | None, Some _ -> begin
	P.eprintf "%a: dexp2_while_tr_up_init: not preserved variable: %a\n"
	  Loc.fprint loc fprint_dvar2 d2v;
	Err.abort ();
      end
    | Some _, None ->  begin
	P.eprintf "%a: dexp2_while_tr_up_init: not consumed variable: %a\n"
	  Loc.fprint loc fprint_dvar2 d2v;
	Err.abort ();
      end in
    List.iter aux inv.loopinv2_arg

and dexp2_while_tr_up_start
  (inv: loopinv2): (sexp2 list) option * statype2 =
  let loc = inv.loopinv2_loc in
  let sub =
    SEnv3.sexp2_hypo_inst_and_add loc
      inv.loopinv2_svs inv.loopinv2_gua in
  let inv_met = match inv.loopinv2_met with
    | Some s2es ->
	let s2es = sexp2_list_subst sub s2es in
	  (SEnv3.metric_check loc s2es; Some s2es)
    | None -> None in
  let inv_arg = statype2_body_subst sub inv.loopinv2_arg in
  let sty_exit =
    let inv_res = match inv.loopinv2_res with
      | None -> statype2_nil | Some sty -> sty in
    let inv_res_svs = inv_res.statype2_svs in
    let inv_res_gua =
      sexp2_list_subst sub inv_res.statype2_gua in
    let inv_res_body =
      statype2_body_subst sub inv_res.statype2_body in
      statype2_make inv_res_svs inv_res_gua
	None(*metric*) (inv_res_body @ inv_arg) in
  let () =
    let rec aux (d2v, os2e) = match os2e with
      | Some s2e ->
	  let s2e = SEnv3.sexp2_open_and_add s2e in
	    d2v.dvar2_type <- Some s2e
      | None -> d2v.dvar2_type <- None in List.iter aux inv_arg in
    (inv_met, sty_exit)
  
(* ****** ****** *)

and dexp2_tr_dn
  (d2e0: dexp2) (s2e0: sexp2): dexp3 = begin
  match d2e0.dexp2_node with
    | DE2top -> begin
	dexp3_top (d2e0.dexp2_loc) (sexp2_topize s2e0)
      end
    | _ -> begin
	let d3e0 = dexp2_tr_dn_main d2e0 s2e0 in
	let () = d3e0.dexp3_type <- s2e0 in d3e0
      end
end (* end of [dexp2_tr_dn] *)

and dexp2_tr_dn_main (d2e0: dexp2) (s2e0: sexp2): dexp3 =
(*
  let () = P.fprintf stdout "dexp2_tr_dn_main:\n" in
  let () = P.fprintf stdout "  d2e0 = %a\n" fprint_dexp2 d2e0 in
  let () = P.fprintf stdout "  s2e0 = %a\n" fprint_sexp2 s2e0 in
*)
  let loc0 = d2e0.dexp2_loc in
  let s2e0 = sexp2_whnf s2e0 in match d2e0.dexp2_node with
    | DE2arr (s2e_elt, d2es_elt) -> begin
	dexp2_arr_tr_dn loc0 s2e_elt d2es_elt s2e0
      end (* end of [DE2arr] *)

    | DE2case (sgn, osty, d2es, c2ls) -> begin
	let sty = match osty with
	  | None -> statype2_nil | Some sty -> sty in
	let d3es = dexp2_list_tr_up d2es in
	let () = dexp3_list_open_and_add d3es in
	let s2es = type_of_dexp3_list d3es in
	let c3ls = cla2_list_tr loc0 sgn sty c2ls (Some d3es) s2es s2e0 in
	  dexp3_case loc0 sgn s2e0 d3es c3ls
      end (* end of [DE2case] *)

    | DE2effmask (eff, d2e) -> begin
	let () = SEnv3.effenv_push_with_effmask eff in
	let d3e = dexp2_tr_dn d2e s2e0 in
	let () = SEnv3.effenv_pop () in d3e
      end (* end of [DE2effmask] *)

    | DE2exi (s2a, d2e) -> begin
	let s2e0 = SEnv3.sexp2_exi_inst_sexparg2 loc0 s2e0 s2a in
	  dexp2_tr_dn d2e s2e0
      end (* end of [DE2exi] *)

    | DE2fix (d2v_fun, d2e_def) -> begin
	let () = d2v_fun.dvar2_master_type <- s2e0 in
	let s2e = SEnv3.sexp2_open_and_add s2e0 in
	let () = d2v_fun.dvar2_type <- Some s2e in
	let d3e_def = dexp2_tr_dn d2e_def s2e0 in
	  dexp3_fix loc0 d2v_fun d3e_def
      end (* end of [DE2fix] *)

    | DE2int (Syn.IKint, i) -> dexp2_int_tr_dn loc0 i s2e0

    | DE2if (osty, d2e1, d2e2, od2e3) -> begin
	let sty = match osty with
	  | None -> statype2_nil | Some sty -> sty in
	let d3e1 = dexp2_tr_up d2e1 in
	let c2l1 = cla2_of_dexp2_if true d2e2 in
	let c2l2 = cla2_of_dexp2_if_opt false od2e3 in
	let s2e_cond =
	  let () = dexp3_open_and_add d3e1 in d3e1.dexp3_type in
	let s2e0 = match od2e3 with
	  | None ->
	      let s2e = sexp2_void_t0ype () in
	      let () = SOL.sexp2_tyleq_solve loc0 s2e s2e0 in s2e
	  | Some _ -> s2e0 in
	let c3ls =
	  cla2_list_tr loc0
	    0 (*sgn*) sty [c2l1; c2l2] None [s2e_cond] s2e0 in
	  match c3ls with
	    | [c3l1; c3l2] ->
		dexp3_if loc0 s2e0 d3e1 c3l1.cla3_body c3l2.cla3_body
	    | _ -> error_of_deadcode "ats_trans3: dexp2_tr_dn: DE2if"
      end (* [DE2if] *)

    | DE2lam_dyn (is_lin, (npf, p2ts), d2e) -> begin
(*
	let () =
	  P.fprintf stdout "dexp2_tr_dn: DE2lam_dyn: p2ts = %a\n"
	    fprint_pat2_list p2ts in
	let () =
	  P.fprintf stdout "dexp2_tr_dn: DE2lam_dyn: d2e = %a\n"
	    fprint_dexp2 d2e in
*)
	let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
	  | SE2clo (knd, s2e_fun) -> 
	      let fc_fun = Syn.FUNCLOclo knd in
		dexp2_lam_dyn_tr_dn loc0 is_lin npf p2ts d2e fc_fun s2e_fun
	  | SE2fun _ ->
	      let fc_fun = Syn.FUNCLOfun in
		dexp2_lam_dyn_tr_dn loc0 is_lin npf p2ts d2e fc_fun s2e0
	  | SE2uni (s2vs, s2ps, s2e) ->
	      let () = SEnv3.env_push () in
	      let () = SEnv3.svar_list_add s2vs in
	      let () = SEnv3.hypo_prop_list_add s2ps in
	      let d3e0 = dexp2_tr_dn d2e0 s2e in
	      let () = SEnv3.env_pop_and_add () in
		d3e0
	  | _ -> begin
	      let d3e0 = dexp2_tr_up d2e0 in (dexp3_tr_dn d3e0 s2e0; d3e0)
	    end
      end (* end of [DE2lam_dyn] *)

    | DE2let (d2cs, d2e) -> begin
	let () = SEnv3.effenv_push () in
	let () = SEnv3.scst2_push () in
	let () = DEnv3.env_push_let () in
	let d3cs = dec2_list_tr d2cs in
	let d3e = dexp2_tr_dn d2e s2e0 in
	let () = DEnv3.dynenv_final_check loc0 in
	let () = DEnv3.env_pop_let () in
	let () = SEnv3.scst2_pop_and_unbind () in
	let () = SEnv3.effenv_pop () in
	  dexp3_let loc0 d3cs d3e
      end (* end of [DE2let] *)

    | DE2lst d2es -> begin match un_sexp2_list_t0ype_int_type s2e0 with
	| Some (s2e_elt, s2e_sz) ->
	    let int_sz = List.length d2es in
	    let d3es = List.map (function d2e -> dexp2_tr_dn d2e s2e_elt) d2es in
	    let () = SOL.sexp2_equal_solve loc0 s2e_sz (sexp2_int int_sz) in
	      dexp3_lst loc0 s2e0 d3es
	| None ->
	    let int_sz = List.length d2es in
	    let s2e_elt = SEnv3.sexp2_Var_new loc0 srt2_t0ype in
	    let s2e_lst = sexp2_list_t0ype_int_type s2e_elt int_sz in
	    let d3es = List.map (function d2e -> dexp2_tr_dn d2e s2e_elt) d2es in
	    let () = SOL.sexp2_tyleq_solve loc0 s2e_lst s2e0 in
	      dexp3_lst loc0 s2e0 d3es
      end (* end of [DE2lst] *)

    | DE2raise (d2e) -> begin
	let () = SEnv3.effenv_check_exn loc0 in
	let d3e = dexp2_tr_dn d2e (Exception_viewtype.make_exp None) in
	  dexp3_raise loc0 d3e
      end (* end of [DE2raise] *)

    | DE2rec (is_flat1, (npf1, ld2es)) -> begin match s2e0.sexp2_node with
	| SE2tyrec (k2, (npf2, ls2es)) ->
	    let () = match is_flat1 with
	      | true -> begin match k2 with
		  | TYRECflt _ -> () | TYRECbox -> EM3.flatness_errmsg loc0 k2
		end
	      | false -> begin match k2 with
		  | TYRECflt _ -> EM3.flatness_errmsg loc0 k2 | TYRECbox -> ()
		end in
	    let () = if npf1 <> npf2 then EM3.pfarity_errmsg loc0 in
	    let ld3es = labdexp2_list_tr_dn loc0 ld2es ls2es in
		dexp3_rec loc0 s2e0 is_flat1 npf1 ld3es
(*
	| SE2vararg s2e_arg ->
	    let () = if not (is_flat1) then EM3.flatness_errmsg loc0 in
	    let () = if npf1 > 0 then EM3.pfarity_errmsg loc0 in
	    let d2es = List.map (function (l, d2e) -> d2e) ld2es in
	    let d3es = dexp2_list_tr_dn_vararg loc0 d2es s2e_arg in
	      dexp3_vararg loc0 s2e0 d3es
*)
	| _ -> begin
	    let ld3es = labdexp2_list_tr_up ld2es in
	    let ls2es = type_of_labdexp3_list ld3es in
	    let k1 = tyrec_kind_of_flatness is_flat1 in
	    let () =
	      SOL.labsexp2_list_tyrec_tyleq_solve loc0 k1 npf1 ls2es s2e0 in
	      dexp3_rec loc0 s2e0 is_flat1 npf1 ld3es
	  end
      end (* end of [DE2rec] *)

    | DE2seq d2es -> dexp2_seq_tr loc0 d2es (Some s2e0)

    | DE2sif (s2p1, d2e2, d2e3) -> dexp2_sif_tr_dn loc0 s2p1 d2e2 d2e3 s2e0

    | DE2string s -> begin
	match un_sexp2_printf_c_types_type s2e0 with
	  | Some s2e -> begin
	      let fas = match PFc.printf_c_string_parse s with
		| Some fas -> fas
		| None -> begin
		    P.eprintf "%a: illegal format string.\n" Loc.fprint loc0;
		    Err.abort ();
		  end in
	      let s2e_fas = sexp2_of_printf_c_argtypes fas in
(*
	      let () =
		P.fprintf stdout
		  "dexp2_tr_dn: DE2string: s2e_fas = %a\n" fprint_sexp2 s2e_fas in
	      let () =
		P.fprintf stdout
		  "dexp2_tr_dn: DE2string: s2e = %a\n" fprint_sexp2 s2e in
*)
              (* printf_c_types_type is contravariant! *)
	      let () = SOL.sexp2_tyleq_solve loc0 s2e s2e_fas in
		dexp3_special_string loc0 s2e0 s
	    end (* end of [Some] *)
	  | None -> let d3e0 = dexp3_string loc0 s in (dexp3_tr_dn d3e0 s2e0; d3e0)
      end (* end of [DE2string] *)

    | DE2struct ld2es -> begin
	match s2e0.sexp2_node with
	  | SE2tyrec (k, (npf, ls2es)) ->
	      let () =
		begin match k with
		  | TYRECflt _ -> () | TYRECbox -> EM3.flatness_errmsg loc0 k
		end in
	      let () = if npf > 0 then EM3.pfarity_errmsg loc0 in
	      let ld3es = labdexp2_list_tr_dn loc0 ld2es ls2es in
		dexp3_struct_with_type loc0 s2e0 ld3es
	  | _ -> begin
	      let ld3es = labdexp2_list_tr_up ld2es in
	      let ls2es = type_of_labdexp3_list ld3es in
	      let k = TYRECflt Cnt.zero in 
	      let () =
		SOL.labsexp2_list_tyrec_tyleq_solve loc0 k 0 (* npf *) ls2es s2e0 in
		dexp3_struct_with_type loc0 s2e0 ld3es
	    end (* end of [_] *)
      end (* end of [DE2struct] *)

    | DE2trywith (d2e, c2ls) -> begin
	let () = DEnv3.env_push_try () in
	let d3e = dexp2_tr_dn d2e s2e0 in
	let s2e_exn = Exception_viewtype.make_exp None in
	let c3ls = (* no warning on exhaustiveness *)
	  cla2_list_tr loc0
	    (-1) (*sgn*) statype2_nil c2ls None [s2e_exn] s2e0 in 
	let () = DEnv3.env_pop_try () in
	  dexp3_trywith loc0 d3e c3ls
      end (* end of [DE2trywith] *)

    | _ -> let d3e0 = dexp2_tr_up d2e0 in (dexp3_tr_dn d3e0 s2e0; d3e0)

(* ****** ****** *)

and dexp23_arg_list_tr_dn loc0
  (d23es: dexp23 list) (s2es: sexp2 list): dexp3 list =
  let aux d23e s2e = match d23e with
    | DE23dexp2 d2e -> dexp2_tr_dn d2e s2e
    | DE23dexp3 d3e -> (dexp3_tr_dn d3e s2e; d3e) in
    match compare (List.length d23es) (List.length s2es) with
      | 0 -> List.map2 aux d23es s2es
      | i -> arity_errmsg loc0 i

(* ****** ****** *)

and dexp2_opt_tr_dn od2e s2e: dexp3 option = match od2e with
  | None -> None | Some d2e -> Some (dexp2_tr_dn d2e s2e)

(* ****** ****** *)

and labdexp2_list_tr_dn loc0
  (ld2es: labdexp2 list) (ls2es: labsexp2 list): labdexp3 list =
  let rec aux ld3es ld2es ls2es = match ld2es, ls2es with
    | [], [] -> List.rev ld3es
    | (l1, d2e) :: ld2es, (l2, s2e) :: ls2es ->
	if Lab.eq l1 l2 then
	  aux ((l1, dexp2_tr_dn d2e s2e) :: ld3es) ld2es ls2es
	else labdexp2_label_errmsg d2e.dexp2_loc l1 l2
    | _, _ -> error_of_deadcode "ats_trans3: labdexp2_list_tr_dn: aux" in
    match compare (List.length ld2es) (List.length ls2es) with
      | 0 -> aux [] ld2es ls2es
      | i -> labdexp2_length_errmsg loc0 i

(* ****** ****** *)

and dexp2_arr_tr_dn loc0
  (s2e_elt: sexp2) (d2es_elt: dexp2 list) (s2e0: sexp2): dexp3 =
  let d3e = dexp2_arr_tr_up loc0 s2e_elt d2es_elt in
    (dexp3_tr_dn d3e s2e0; d3e)

(* ****** ****** *)

and dexp2_int_tr_dn loc0 (i: intinf) (s2e0: sexp2): dexp3 =
  let s2e_hd = sexp2_head s2e0 in match s2e_hd.sexp2_node with
    | SE2cst s2c when Int_t0ype.eq_cst s2c ->
	dexp3_int_with_type loc0 Syn.IKint (Int_t0ype.make_exp None) i
    | SE2cst s2c when Uint_t0ype.eq_cst s2c -> 
	dexp3_int_with_type loc0 Syn.IKuint (Uint_t0ype.make_exp None) i
    | SE2cst s2c when Uint_int_t0ype.eq_cst s2c -> begin
	let s2e = sexp2_uint_int_t0ype i in
	let () = SOL.sexp2_tyleq_solve loc0 s2e s2e0 in
	  dexp3_int_with_type loc0 Syn.IKuint s2e0 i
      end (* SE2cst _ when ... *)
    | SE2cst s2c when Size_int_t0ype.eq_cst s2c -> begin
        let s2e = sexp2_size_int_t0ype i in
        let () = SOL.sexp2_tyleq_solve loc0 s2e s2e0 in
          dexp3_int_with_type loc0 Syn.IKulint s2e0 i
      end (* SE2cst _ when ... *)          
    | _ -> begin
	let d3e0 = dexp3_int loc0 Syn.IKint i in
	  (dexp3_tr_dn d3e0 s2e0; d3e0)
      end (* _ *)

(* ****** ****** *)

and dexp2_lam_dyn_tr_dn loc0 (is_lin: bool)
  (npf: int) (p2ts: pat2 list) (d2e: dexp2)
  (fc_fun: Syn.funclo) (s2e_fun: sexp2): dexp3 = begin
  match s2e_fun.sexp2_node with
    | SE2fun (lin_fun, sf2e_fun, (npf_fun, s2es_fun_arg), s2e_fun_res) ->
	let () = SEnv3.env_push () in
	let (d2e, ofc) = dexp2_funclo_opt_of_dexp2 d2e in
	let fc = match ofc with
	  | Some fc -> (SOL.funclo_equal_solve loc0 fc_fun fc; fc)
	  | None -> fc_fun in
	let lin = if is_lin then 1 else 0 in
	let () = SOL.funlinear_equal_solve loc0 lin lin_fun in
	let (d2e, osf2e) = dexp2_seff2_opt_of_dexp2 d2e in
	let sf2e = match osf2e with
	  | Some sf2e ->
	      (SOL.sexp2_eff_leq_solve loc0 sf2e sf2e_fun; sf2e)
	  | None -> sf2e_fun in
	let () = SEnv3.effenv_push_with_lam sf2e in
	let () = DEnv3.env_push_lam is_lin in
	let () = DEnv3.lamloop_push_lam () in
	let () = List.iter DEnv3.pat2_dvs_add_local p2ts in
	let p3ts = pat2_arg_list_tr_dn loc0 npf p2ts s2es_fun_arg in
	let d3e = dexp2_tr_dn d2e s2e_fun_res in
	let () = DEnv3.dynenv_final_check loc0 in
	let () = if is_lin then DEnv3.dynenv_final_check_llam loc0 in
	let () = DEnv3.lamloop_pop () in
	let () = DEnv3.env_pop_lam () in
	let () = SEnv3.effenv_pop () in
	let () = SEnv3.env_pop_and_add () in
	  dexp3_lam_dyn loc0 fc is_lin sf2e (npf, p3ts) d3e
    | _ -> begin
	error_of_deadcode "dexp2_lam_dyn_tr_dn: s2e_fun: not function type"
      end
end (* end of [dexp2_lam_dyn_tr_dn] *)

(* ****** ****** *)

and dexp2_sif_tr_dn loc0
  (s2p1: sexp2) (d2e2: dexp2) (d2e3: dexp2) (s2e: sexp2): dexp3 =
  let sbis = DEnv3.state_before_save () in
  let sas = DEnv3.state_afters_initialize sbis in
  let d3e2 =
    let () = SEnv3.env_push () in
    let () = SOL.sexp2_hyeq_solve loc0 s2p1 (sexp2_bool true) in
    let d3e = dexp2_tr_dn d2e2 s2e in
    let () = DEnv3.state_afters_merge d2e2.dexp2_loc sas sbis in
    let () = SEnv3.env_pop_and_add () in
      d3e in
  let d3e3 =
    let () = DEnv3.state_before_restore sbis in
    let () = SEnv3.env_push () in
    let () = SOL.sexp2_hyeq_solve loc0 s2p1 (sexp2_bool false) in
    let d3e = dexp2_tr_dn d2e3 s2e in
    let () = DEnv3.state_afters_merge d2e3.dexp2_loc sas sbis in
    let () = SEnv3.env_pop_and_add () in
      d3e in
  let () = begin
      DEnv3.state_check_with_before_and_afters loc0 sbis sas;
      DEnv3.state_update_with_before_and_afters loc0 sbis sas
  end in
    dexp3_sif loc0 s2e s2p1 d3e2 d3e3

(* ****** ****** *)

and dexp2_seq_tr loc0
  (d2es0: dexp2 list) (os2e: sexp2 option): dexp3 =
  let rec aux d3es d2e d2es = match d2es with
    | d2e_new :: d2es_new ->
	let d3e = dexp2_tr_up d2e in
	let () = dexp3_open_and_add d3e in
	let () =
	  SOL.sexp2_tyleq_solve d3e.dexp3_loc
	    d3e.dexp3_type (sexp2_void_t0ype ()) in
	  aux (d3e :: d3es) d2e_new d2es_new
    | [] -> begin
	let d3e = match os2e with
	  | None -> dexp2_tr_up d2e
	  | Some s2e -> dexp2_tr_dn d2e s2e in
	let d3es = List.rev (d3e :: d3es) in
	  dexp3_seq_with_type loc0 d3e.dexp3_type d3es
      end in
    match d2es0 with
      | d2e :: d2es -> aux [] d2e d2es | [] -> dexp3_empty loc0

(* ****** ****** *)

and cla2_tr
  (op2tcss: patcst2 list list option) (c2l: cla2)
  (n0:int) (od3es: (dexp3 list) option) (s2es: sexp2 list) (s2e: sexp2)
  (sbis_sas_opt: (DEnv3.state_before * DEnv3.state_afters) option): cla3 =
  let loc = c2l.cla2_loc in
  let p2ts = c2l.cla2_pat in
  let () = match compare (List.length p2ts) n0 with
    | 0 -> () | i -> cla2_tr_errmsg loc i in
(*
  let () =
    P.fprintf stdout "cla2_tr: p2ts = (%a)\n" fprint_pat2_list p2ts in
  let () =
    P.fprintf stdout "cla2_tr: s2es = (%a)\n" fprint_sexp2_list s2es in
*)
(*
  let () =
    P.fprintf stdout
      "cla2_tr: before: stamps = (%a)\n" fprint_stamps (SS.stamps_get ()) in
*)
  let () = SEnv3.env_push () in
  let () = DEnv3.env_push_let () in
  let () = List.iter DEnv3.pat2_dvs_add_local p2ts in
  let () = match op2tcss with
    | Some p2tcss -> patcst2_list_list_cstr_add loc p2tcss s2es
    | None -> () in
  let p3ts = pat2_list_tr_dn loc p2ts s2es in
  let () = match od3es with
    | Some d3es -> List.iter2 dexp3_lval_type_update_pat3 d3es p3ts
    | None -> () in
(*
  let () =
    P.fprintf stdout
      "cla2_tr: after: stamps = (%a)\n" fprint_stamps (SS.stamps_get ()) in
*)
  let gua = match c2l.cla2_gua with
    | Some d2e_when ->
	let d3e_when = dexp2_tr_up d2e_when in
	let () = pat2_assert_tr_dn d3e_when.dexp3_loc d3e_when.dexp3_type in
	  Some d3e_when
    | None -> None in
  let d3e =
    let s2e_none = sexp2_none_viewt0ype () in
      if c2l.cla2_isneg then dexp2_tr_dn c2l.cla2_body s2e_none
      else dexp2_tr_dn c2l.cla2_body s2e in
  let () = match sbis_sas_opt with
    | Some (sbis, sas) ->
	if not (cla2_is_raised c2l) then DEnv3.state_afters_merge loc sas sbis
    | None -> () in
  let () = DEnv3.dynenv_final_check loc in
  let () = DEnv3.env_pop_let () in
  let () = SEnv3.env_pop_and_add () in
    cla3 loc p3ts gua op2tcss c2l.cla2_isneg d3e

and cla2_list_tr loc0 (sgn: int) (sty: statype2) (c2ls: cla2 list)
  (od3es: (dexp3 list) option) (s2es: sexp2 list) (s2e: sexp2): cla3 list =
  match c2ls with
    | [] -> cla2_list0_tr s2es s2e
    | c2l :: [] -> cla2_list1_tr loc0 sgn c2l od3es s2es s2e
    | c2l :: c2ls -> cla2_list2_tr loc0 sgn sty c2l c2ls od3es s2es s2e

and cla2_list0_tr (s2es: sexp2 list) (s2e: sexp2): cla3 list =
  error_of_unavailability "ats_trans3: cla2_list0_tr: unavaiable yet"

and cla2_list1_tr loc0 (sgn: int) (c2l: cla2)
  (od3es: (dexp3 list) option) (s2es: sexp2 list) (s2e: sexp2): cla3 list =
  let n = List.length s2es in
  let c3l = cla2_tr None c2l n od3es s2es s2e None in
  let p2tcss = cla2_pat_comp c2l in
  let () = pattern_match_is_nonexhaustive_check loc0 sgn p2tcss s2es in
    [c3l]

and cla2_list2_tr loc0
  (sgn: int) (sty: statype2) (c2l: cla2) (c2ls: cla2 list)
  (od3es: (dexp3 list) option) (s2es: sexp2 list) (s2e: sexp2): cla3 list =
(*
  let () =
    let aux c2l =
      P.fprintf stdout "cla2_list2_tr: p2ts = (%a)\n"
	fprint_pat2_list c2l.cla2_pat in
      List.iter aux (c2l :: c2ls) in
  let () =
    P.fprintf stdout "cla2_list2_tr: s2es = (%a)\n"
      fprint_sexp2_list s2es in
*)
  let n = List.length s2es in
  let sbis = DEnv3.state_before_save () in
  let sas = DEnv3.state_afters_initialize sbis in
  let p2tcss = cla2_pat_comp c2l in
  let c3l = cla2_tr None c2l n od3es s2es s2e (Some (sbis, sas)) in
    cla2_list2_rest_tr loc0 sgn sty c3l p2tcss c2ls n od3es s2es s2e sbis sas

and cla2_list2_rest_tr loc0 (sgn: int) (sty: statype2)
  (c3l_first: cla3) (p2tcss: patcst2 list list) (c2ls: cla2 list)
  (n: int) (od3es: (dexp3 list) option) (s2es: sexp2 list) (s2e: sexp2)
  (sbis: DEnv3.state_before) (sas: DEnv3.state_afters): cla3 list =
  let rec aux c3ls p2tcss0 c2ls0 = match c2ls0 with
    | [] -> (p2tcss0, List.rev c3ls)
    | c2l :: c2ls ->
	let p2tcs0 = patcst2_of_pat2_list c2l.cla2_pat in
(*
	let () =
	  P.fprintf stdout
	    "cla2_list2_rest_tr: p2tcs0 = %a\n" fprint_patcst2_list p2tcs0 in
	let () =
	  P.fprintf stdout
	    "cla2_list2_rest_tr: p2tcss0 = %a\n" fprint_patcst2_list_list p2tcss0 in
*)
	let p2tcss1 =
	  List.filter
	    (function p2tcs -> patcst2_list_is_ints p2tcs p2tcs0) p2tcss0 in
(*
	let () =
	  P.fprintf stdout
	    "cla2_list2_rest_tr: p2tcss1 = %a\n" fprint_patcst2_list_list p2tcss1 in
*)
	let () = match p2tcss1 with
	  | _ :: _ -> ()
	  | [] -> begin match sgn with
	      | (0 | 1) -> pattern_match_is_redundant_errmsg c2l.cla2_loc
	      | _ -> ()	      
	    end in

	let op2tcss = if c2l.cla2_isseq then Some p2tcss1 else None in

	let p2tcss2 = match c2l.cla2_gua with
	  | None -> List.fold_right
	      (fun p2tcs res -> patcst2_list_diff p2tcs p2tcs0 @ res) p2tcss0 []
	  | Some _ -> p2tcss0 in
(*
	let () =
	  P.fprintf stdout
	    "cla2_list2_rest_tr: p2tcss2 = %a\n" fprint_patcst2_list_list p2tcss2 in
*)
	let () = DEnv3.state_before_restore sbis in
	let c3l = cla2_tr op2tcss c2l n od3es s2es s2e (Some (sbis, sas)) in
      aux (c3l :: c3ls) p2tcss2 c2ls in
  let (p2tcss_left, c3ls)  = aux [] p2tcss c2ls in
(*
  let () =
    P.fprintf stdout
      "cla2_list2_rest_tr: p2tcss_left = %a\n" fprint_patcst2_list_list p2tcss_left in
*)
  let () = pattern_match_is_nonexhaustive_check loc0 sgn p2tcss_left s2es in
  let () =
    DEnv3.state_check_with_before_and_afters_with_state loc0 sbis sas sty in
  let () =
    DEnv3.state_update_with_before_and_afters_with_state loc0 sbis sas sty in
    c3l_first :: c3ls

(* ****** ****** *)

and dec2_fun_tr (stamp: stamp) (d: dec2_fun): dexp3 =
(*
  let () =
    P.fprintf stdout "dec2_fun_tr: %a = %a\n"
      fprint_dvar2 d.dec2_fun_name fprint_dexp2 d.dec2_fun_def in
*)
  let d2v = d.dec2_fun_name in

  let () = SEnv3.env_push () in
  let () =
    let f (s2vs, s2ps) =
      (SEnv3.svar_list_add s2vs; SEnv3.hypo_prop_list_add s2ps) in
      List.iter f d2v.dvar2_decarg in
  let d3e = dexp2_tr_up d.dec2_fun_def in
  let () = SEnv3.env_pop_and_add () in

(*
  let () =
    P.fprintf stdout "dec2_fun_tr: fun %a: %a\n\n"
      fprint_dvar2 d2v fprint_sexp2 d3e.dexp3_type in
*)
  let s2e_gen = sexp2_gen stamp d3e.dexp3_type in
  let () = d3e.dexp3_type <- s2e_gen in
(*
  let () =
    P.fprintf stdout "dec2_fun_tr: fun %a: %a\n"
      fprint_dvar2 d2v fprint_sexp2 s2e_gen in
*)
    d3e

(* [dvar2_add_local] is not called as functions are not linear *)
and dec2_fun_list_tr
  (fk: Syn.funkind) (ds: dec2_fun list): dec3_fun list =
  let is_recursive = Syn.funkind_is_recursive fk in
  let d2vs_fun = List.map (function d -> d.dec2_fun_name) ds in
  let rec aux_ini is_first os2ts0 = function
    | [] -> ()
    | d :: ds ->
	let d2v = d.dec2_fun_name in
	let () = dexp2_lam_met_load d.dec2_fun_def d2vs_fun in
	let (os2ts, s2e) =
	  let s2e = type_of_dexp2 (d.dec2_fun_def) in
(*
	  let () =
	    P.fprintf stdout
	      "dec2_fun_list_tr: d2v = %a and s2e = %a\n"
	      fprint_dvar2 d2v fprint_sexp2 s2e in
	  let () =
	    P.fprintf stdout "dec2_fun_list_tr: d2e = %a\n"
	      fprint_dexp2 d.dec2_fun_def in
*)
	    match Met.sexp2_mfun_load s2e d2v.dvar2_stamp with
	      | None -> (None, s2e)
	      | Some (s2ts, s2e) -> (Some s2ts, s2e) in
	let os2ts0 =
	  if not (is_first) then 
	    let is_consistent = match os2ts0, os2ts with
	      | Some s2ts0, Some s2ts -> srt2_list_leq s2ts0 s2ts
	      | None, None -> true
	      | _, _ -> false in
	      if is_consistent then os2ts0 else
		begin
		  P.eprintf
		    "%a: incompatible termination metrics in mutual recursion.\n"
		    Loc.fprint d.dec2_fun_loc;
		  Err.abort ();
		end
	  else os2ts in
(*
	let () =
	  P.fprintf stdout "dec2_fun_list_tr: aux_ini: fun %a: %a\n\n"
	    fprint_dvar2 d2v fprint_sexp2 s2e in
*)
	let () = d2v.dvar2_master_type <- s2e in
	let () = d2v.dvar2_type <- Some s2e in
	  aux_ini false (* is_first *) os2ts0 ds in
  let aux_fin d d3e =
    let d2v = d.dec2_fun_name in
    let s2e = d3e.dexp3_type in
    let () = d2v.dvar2_master_type <- s2e in
    let () = d2v.dvar2_type <- Some s2e in
      dec3_fun d.dec2_fun_loc d2v d3e in
  let stamp =
    let s2v_dummy = svar2_new srt2_unit in
    let () = SEnv3.svar_add s2v_dummy in
      s2v_dummy.svar2_stamp in
  let () = if is_recursive then aux_ini true None ds in
  let d3es_fun = List.map (dec2_fun_tr stamp) ds in
  let () = SEnv3.stamp_remove stamp in
(*
  let () =
    P.fprintf stdout "dec2_fun_tr_list: stamps = (%a)\n"
      fprint_stamps (SS.stamps_get ()) in
*)
    List.map2 aux_fin ds d3es_fun

(* ****** ****** *)

and dec2_val_tr (vk: Syn.valkind) (d: dec2_val): dec3_val =
  let loc0 = d.dec2_val_loc in
  let p2t = d.dec2_val_pat in
  let is_prf = Syn.valkind_is_proof vk in
  let () = if is_prf then SEnv3.effenv_push_with_lam seff2_nil in
  let d3e_def = match d.dec2_val_ann with
    | Some s2e -> dexp2_tr_dn d.dec2_val_def s2e
    | None -> dexp2_tr_up d.dec2_val_def in
  let () = if is_prf then SEnv3.effenv_pop () in
  let s2e_def = d3e_def.dexp3_type in
(*
  let () =
    P.fprintf stdout "dec2_val_tr: p2t = %a\n"
      fprint_pat2 p2t in
  let () =
    P.fprintf stdout "dec2_val_tr: d3e.dexp2_type = %a\n"
      fprint_sexp2 s2e_def in
*)
  let () =
    if is_prf then pat2_proofize p2t
    else if (sexp2_is_proof s2e_def) then begin
      P.eprintf "%a: the dynamic expression is a proof.\n"
	Loc.fprint d3e_def.dexp3_loc;
      Err.abort ();
    end in
  let () =
    let sgn = Syn.sign_of_valkind vk in
    let p2tcs = [patcst2_of_pat2 p2t] in
    let p2tcss = patcst2_list_comp p2tcs in
      pattern_match_is_nonexhaustive_check loc0 sgn p2tcss [s2e_def] in
  let p3t = pat2_tr_dn p2t s2e_def in
  let () = DEnv3.dvar2_list_add_local p2t.pat2_dvs in
  let () = dexp3_lval_type_update_pat3 d3e_def p3t in
    dec3_val loc0 p3t d3e_def

and dec2_val_list_tr (vk: Syn.valkind) (ds: dec2_val list): dec3_val list =
  List.map (dec2_val_tr vk) ds

and dec2_valpar_list_tr (ds: dec2_val list): dec3_val list =
  List.map (dec2_val_tr Syn.VKval) ds

and dec2_valrec_list_tr (ds: dec2_val list): dec3_val list =
  let rec aux1 res = function
    | d :: ds ->
	let p3t = match d.dec2_val_ann with
	  | Some s2e -> pat2_tr_dn d.dec2_val_pat s2e
	  | None -> pat2_tr_up d.dec2_val_pat in
	  aux1 ((d, p3t) :: res) ds
    | [] -> List.rev res in
  let rec aux2 res = function
    | (d, p3t) :: dp2ts ->
	let loc = d.dec2_val_loc in
	let d3e =
	  dexp2_tr_dn d.dec2_val_def p3t.pat3_type in
	let d3 = dec3_val loc p3t d3e in
	  aux2 (d3 :: res) dp2ts
    | [] -> List.rev res in
    aux2 [] (aux1 [] ds)

(* ****** ****** *)

and dec2_var_tr (is_stack: bool) (d: dec2_var): dec3_var =
  let d2v_ptr = d.dec2_var_dvar in
  let () = DEnv3.dvar2_add_local d2v_ptr in
  let s2e_addr = sexp2_var (d.dec2_var_svar) in
  let () = SEnv3.hypo_prop_add (sexp2_pgt_null s2e_addr) in
  let s2e_ptr = Ptr_addr_type.make_exp (Some [s2e_addr]) in
  let () = d2v_ptr.dvar2_type <- Some s2e_ptr in
  let () = d2v_ptr.dvar2_master_type <- s2e_ptr in
  let d2v_view = DEnv3.dvar2_ptr_viewat_make d2v_ptr in
  let () = d2v_ptr.dvar2_view <- Some d2v_view in (* [d2v_ptr] is mutable *)
  let od3e =
    match d.dec2_var_type, d.dec2_var_ini with
      | None, None -> begin
	  P.eprintf
	    "%a: dec2_var_tr: uninitialized dynamic variable <%a> needs type annotation.\n"
	    Loc.fprint d.dec2_var_loc fprint_dvar2 d2v_ptr;
	  Err.abort ()
	end
      | None, Some d2e ->
	  let d3e = dexp2_tr_up d2e in
	  let () = dexp3_open_and_add d3e in
	  let s2e_elt = d3e.dexp3_type in
	  let s2e_view =
	    sexp2_at_viewt0ype_addr_view s2e_elt s2e_addr in
	  let () = d2v_view.dvar2_type <- Some s2e_view in
	  let s2e_view_final =
	    sexp2_at_viewt0ype_addr_view (sexp2_top s2e_elt) s2e_addr in
	  let () =
	    d2v_view.dvar2_master_type <- s2e_view_final in
	  let () =
	    if is_stack then
	      d2v_view.dvar2_final <- DVFSsome (s2e_view_final)
	    else d2v_view.dvar2_final <- DVFSnone in
	    Some d3e
      | Some s2e0_elt, None ->
	  let () =
	    let s2e = sexp2_at_viewt0ype_addr_view s2e0_elt s2e_addr in
	      d2v_view.dvar2_master_type <- s2e in
	  let s2e_view =
	    let s2e_elt = sexp2_top s2e0_elt in
	      sexp2_at_viewt0ype_addr_view s2e_elt s2e_addr in
	  let () = d2v_view.dvar2_type <- Some s2e_view in
	  let () =
	    if is_stack then d2v_view.dvar2_final <- DVFSsome (s2e_view)
	    else d2v_view.dvar2_final <- DVFSnone in
	    None
      | Some s2e0_elt, Some d2e ->
	  let d3e = dexp2_tr_up d2e in	  
	  let s2e_elt =
	    let () = dexp3_open_and_add d3e in d3e.dexp3_type in
	  let () = SOL.sexp2_tyleq_solve d.dec2_var_loc s2e_elt s2e0_elt in
	  let () =
	    let s2e_view = sexp2_at_viewt0ype_addr_view s2e0_elt s2e_addr in
	      d2v_view.dvar2_master_type <- s2e_view in
	  let () =
	    let s2e_view = sexp2_at_viewt0ype_addr_view s2e_elt s2e_addr in
	      d2v_view.dvar2_type <- Some s2e_view in
	  let () =
	    if is_stack then
	      let s2e_elt = sexp2_top s2e0_elt in
	      let s2e = sexp2_at_viewt0ype_addr_view s2e_elt s2e_addr in
		d2v_view.dvar2_final <-  DVFSsome s2e
	    else d2v_view.dvar2_final <- DVFSnone in
	    Some d3e in
(*
  let () = 
    P.fprintf stdout
      "dec2_var_tr: type of d2v_view = %a\n"
      fprint_sexp2 (type_of_dvar2 Loc.nonloc d2v_view) in
*)
    dec3_var d.dec2_var_loc d2v_ptr d2v_view od3e

and dec2_var_list_tr
  (is_stack: bool) (ds: dec2_var list): dec3_var list =
  let () =
    List.iter (function d -> SEnv3.svar_add d.dec2_var_svar) ds in
    List.map (dec2_var_tr is_stack) ds

(* ****** ****** *)

and dec2_impl_tr (d: dec2_impl): dec3_impl =
  let decarg = d.dec2_impl_decarg in
  let () = SEnv3.env_push () in
  let () =
    let f (s2vs, s2ps) =
      (SEnv3.svar_list_add s2vs; SEnv3.hypo_prop_list_add s2ps) in
      List.iter f decarg in
  let d3e = dexp2_tr_up d.dec2_impl_def in
  let () = SEnv3.env_pop_and_add () in
    dec3_impl d.dec2_impl_loc d.dec2_impl_cst decarg d3e

and dec2_impl_list_tr (ds: dec2_impl list): dec3_impl list =
  List.map dec2_impl_tr ds

(* ****** ****** *)

and dec2_local_tr (loc: loc) (head2: dec2 list) (body2: dec2 list)
  : dec3 = 
  let () = SEnv3.scst2_push () in
  let head3 = dec2_list_tr head2 in
  let () = SEnv3.scst2_push () in
  let body3 = dec2_list_tr body2 in
  let s2cs = SEnv3.scst2_pop () in
  let () = SEnv3.scst2_pop_and_unbind () in
  let () = SEnv3.scst2_list_add s2cs in
    dec3_local loc head3 body3

(* ****** ****** *)

and dec2_list_tr_aux1 (ds: dec2 list) (res: dec3 list): dec3 list =
  match ds with
    | [] -> List.rev res
    | d :: ds -> dec2_list_tr_aux2 d ds res

and dec2_list_tr_aux2
  (d: dec2) (ds: dec2 list) (res: dec3 list): dec3 list =
(*
  let () =
    P.fprintf stdout "dec2_list_tr_aux2: stamps = (%a)\n"
      fprint_stamps (SS.stamps_get ()) in
*)
  match d.dec2_node with
    | DC2stavars xs ->
	let f x =
	  let loc = x.dec2_stavar_loc in
	  let s2v = x.dec2_stavar_var in
	  let () = SEnv3.svar_add s2v in
	  let s2e = SEnv3.sexp2_Var_new_of_svar loc s2v in
	    (SB.svar_add s2v s2e; SEnv3.hypo_bind_add s2v s2e) in
	let () = List.iter f xs in
	  dec2_list_tr_aux1 ds res

    | DC2sasps xs ->
	let f x =
	  SEnv3.scst2_bind_and_add
	    x.dec2_sasp_loc x.dec2_sasp_cst x.dec2_sasp_def in
	let () = List.iter f xs in
	  dec2_list_tr_aux1 ds res

    | DC2extype (name, s2e_def) ->
	let d3 = dec3_extype d.dec2_loc name s2e_def in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2extval (name, d2e_def) ->
	let d3e_def = dexp2_tr_up d2e_def in
	let d3 = dec3_extval d.dec2_loc name d3e_def in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2data (dtk, s2cs) ->
	let d3 = dec3_data d.dec2_loc dtk s2cs in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2dyncsts (dck, d2cs) ->
	let d3 = dec3_dyncsts d.dec2_loc dck d2cs in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2exns d2cs -> 
	let d3 = dec3_exns d.dec2_loc d2cs in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2funs (is_temp, fk, xs) ->
	let ds3 = dec2_fun_list_tr fk xs in
	let d3 = dec3_funs d.dec2_loc is_temp fk ds3 in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2vals (vk, xs) ->
	let ds3 = dec2_val_list_tr vk xs in
	let d3 = dec3_vals d.dec2_loc vk ds3 in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2valpars xs ->
	let ds3 = dec2_valpar_list_tr xs in
	let d3 = dec3_valpars d.dec2_loc ds3 in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2valrecs xs ->
	let ds3 = dec2_valrec_list_tr xs in
	let d3 = dec3_valrecs d.dec2_loc ds3 in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2vars (is_stack, xs) ->
	let ds3 = dec2_var_list_tr is_stack xs in
	let d3 = dec3_vars d.dec2_loc is_stack ds3 in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2impls xs ->
	let ds3 = dec2_impl_list_tr xs in
	let d3 = dec3_impls d.dec2_loc ds3 in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2local (head, body) ->
	let d3 = dec2_local_tr d.dec2_loc head body in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2staload (f, oxs) ->
	let ods3 = match oxs with
	  | Some xs -> begin
	      let () = SEnv3.scst2_push () in
	      let ds3 = dec2_list_tr xs in
	      let () = SEnv3.scst2_pop_and_unbind () in
		Some ds3
	    end
	  | None -> None in
	let d3 = dec3_staload d.dec2_loc f ods3 in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2dynload f ->
	let d3 = dec3_dynload d.dec2_loc f in
	  dec2_list_tr_aux1 ds (d3 :: res)

    | DC2extern (position, code) ->
	let d3 = dec3_extern d.dec2_loc position code in
	  dec2_list_tr_aux1 ds (d3 :: res)

and dec2_list_tr (ds: dec2 list): dec3 list = dec2_list_tr_aux1 ds []

(* ****** ****** *)

let initialize () = begin
  (stacst2_initialize (); SEnv3.initialize (); DEnv3.initialize ())
end

let finalize (): SEnv3.cstr3 =
 let s3is = SEnv3.sitem3_list_get () in
 let () = (SS.initialize (); SB.initialize ()) in
   SEnv3.cstr3_itms (List.rev s3is)

(* ****** ****** *)

(* end of [ats_trans3.ml] *)
