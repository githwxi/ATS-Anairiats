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

open Ats_patcst2
open Ats_dynexp3

(* ****** ****** *)

module Cnt = Ats_counter
module Err = Ats_error
module EM2 = Ats_errmsg2
module EM3 = Ats_errmsg3
module Loc = Ats_location

module SEnv3 = Ats_staenv3
module DEnv3 = Ats_dynenv3
module SOL = Ats_staexp2_solve
module Tr2 = Ats_trans2

(* ****** ****** *)

type loc = Loc.location
type stamp = Cnt.count

(* ****** ****** *)

(* a standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_pat_trans3: "; Err.error s;
end

(* ****** ****** *)

let rec type_of_pat2 (p2t: pat2): sexp2 =
  match p2t.pat2_node with
    | PT2ann (_, s2e) -> s2e
    | PT2any ->
	let s2e = SEnv3.sexp2_VarApp_new p2t.pat2_loc srt2_t0ype in
	let () = p2t.pat2_type <- Some s2e in s2e
    | PT2bool b -> sexp2_bool_bool_t0ype b
    | PT2char c -> sexp2_char_char_t0ype c
    | PT2con _ ->
	let s2e = SEnv3.sexp2_VarApp_new p2t.pat2_loc srt2_t0ype in
	let () = p2t.pat2_type <- Some s2e in s2e
    | PT2empty -> sexp2_void_t0ype ()
    | PT2exi (_, p2t) -> begin
	P.eprintf "%a: type_of_pat2: existentially quantified pattern.\n"
	  Loc.fprint p2t.pat2_loc;
	Err.abort ();
      end
    | PT2int i -> sexp2_int_int_t0ype i
    | PT2list _ -> error_of_deadcode "ats_trans3: type_of_pat2: PT2list"
    | PT2lst p2ts ->
	let s2e = SEnv3.sexp2_VarApp_new p2t.pat2_loc srt2_type in
	let () = p2t.pat2_type <- Some s2e in s2e
    | PT2rec (is_flat, is_omit, (npf, lp2ts)) -> begin
	if not (is_omit) then
	  let ls2es = type_of_labpat2_list lp2ts in
	  let k = tyrec_kind_of_flatness is_flat in
	    sexp2_tyrec k npf ls2es
	else
	  let s2t = if is_flat then srt2_t0ype else srt2_type in
	  let s2e = SEnv3.sexp2_VarApp_new p2t.pat2_loc s2t in
	  let () = p2t.pat2_type <- Some s2e in s2e
      end
    | PT2string s -> sexp2_string_int_type s
    | PT2var (_, d2v, op2t) -> begin match op2t with
	| Some p2t -> type_of_pat2 p2t
	| None -> (* the variable is assumed to be nonlinear *)
	    let s2e = SEnv3.sexp2_VarApp_new p2t.pat2_loc srt2_t0ype in
	    let () = p2t.pat2_type <- Some s2e in s2e
      end
    | PT2vbox d2v ->
	let s2e_view =
           (SEnv3.sexp2_VarApp_new p2t.pat2_loc srt2_view) in
	let s2e = Vbox_view_prop.make_exp (Some [s2e_view]) in
	let () = p2t.pat2_type <- Some s2e in s2e	  
(* end of [type_of_pat2] *)

and type_of_pat2_list (p2ts: pat2 list): sexp2 list =
  List.map type_of_pat2 p2ts

and type_of_labpat2_list (lp2ts: labpat2 list): labsexp2 list =
  List.map (function (l, p2t) -> (l, type_of_pat2 p2t)) lp2ts

(* ****** ****** *)

let pat3_confree_tr (p3t0: pat3): unit =
  let (freeknd, d2c, p3ts) = match p3t0.pat3_node with
    | PT3con (freeknd, d2c, (_(*npf*), p3ts)) -> (freeknd, d2c, p3ts)
    | _ -> error_of_deadcode "ats_trans3_pat: pat3_confree_tr" in
  let aux_var (d2v_ptr: dvar2) (s2e_elt: sexp2): dvar2 * sexp2 =
    let name = Syn.sid_of_did d2v_ptr.dvar2_name in
    let s2v_addr = svar2_new_with_id name srt2_addr in
    let () = SEnv3.svar_add s2v_addr in
    let s2e_addr = sexp2_var s2v_addr in
    let s2e_ptr = Ptr_addr_type.make_exp (Some [s2e_addr]) in
    let () = d2v_ptr.dvar2_linear <- (-1) in
    let () = d2v_ptr.dvar2_addr <- Some s2e_addr in
    let () = d2v_ptr.dvar2_type <- Some s2e_ptr in
    let () = d2v_ptr.dvar2_master_type <- s2e_ptr in
    let d2v_view = DEnv3.dvar2_ptr_viewat_make d2v_ptr in
    let s2e_view =
      sexp2_at_viewt0ype_addr_view s2e_elt s2e_addr in
    let () = d2v_view.dvar2_type <- Some s2e_view in
    let () = d2v_view.dvar2_master_type <- s2e_view in
    let () = d2v_view.dvar2_final <- DVFSnone in
      (d2v_view, s2e_addr) in
  let aux_pat p3t =
    let s2e_elt = p3t.pat3_type in
    let (d2v_ptr, op3t_as) = match p3t.pat3_node with
      | PT3any (d2v) -> (d2v, None)
      | PT3var (true, d2v, op3t) -> (d2v, op3t)
      | _ -> begin
	  let d2v = dvar2_new p3t.pat3_loc false (* is_fixed *) in
	    (d2v, Some p3t)
	end in
    let (d2v_view, s2e_addr) = aux_var d2v_ptr s2e_elt in
    let s2e_elt_new = match op3t_as with
      | Some p3t_as ->
	  let s2e_elt_new =
	    if sexp2_is_linear s2e_elt then sexp2_top s2e_elt else s2e_elt in
	  let s2e_view = sexp2_at_viewt0ype_addr_view s2e_elt_new s2e_addr in
	    (d2v_view.dvar2_type <- Some s2e_view; s2e_elt_new)
      | None -> s2e_elt in
    let () =
      if freeknd < 0 then begin
	let () =
          if sexp2_is_linear s2e_elt_new then begin
            P.eprintf "%a: a value matching this pattern may not be freed.\n"
	      Loc.fprint p3t0.pat3_loc;
            Err.abort ()
          end in
          d2v_view.dvar2_type <- None
      end in
      s2e_addr in
  let s2es_addr = List.map aux_pat p3ts in
    if freeknd > 0 then begin
      p3t0.pat3_type_left <- Some (sexp2_datcon d2c s2es_addr)
    end
(* end of [pat3_confree_tr] *)

(* ****** ****** *)

let rec pat2_tr_up (p2t0: pat2): pat3 =
  let loc0 = p2t0.pat2_loc in match p2t0.pat2_node with
    | PT2ann (p2t, s2e) -> pat2_tr_dn p2t s2e
    | PT2any -> begin
	let s2e = SEnv3.sexp2_VarApp_new loc0 srt2_t0ype in
	let d2v = dvar2_new_any loc0 in pat3_any loc0 s2e d2v
      end
    | PT2bool b -> pat3_bool loc0 (sexp2_bool_bool_t0ype b) b
    | PT2char c -> pat3_char loc0 (sexp2_char_char_t0ype c) c
    | PT2con (freeknd, d2c, s2vss, s2pss, s2e, (npf, p2ts)) ->
(*
	let () =
	  P.fprintf stdout "pat2_tr_up: p2t = %a\n" fprint_pat2 p2t0 in		   
	let () =
	  P.fprintf stdout "pat2_tr_up: s2e = %a\n" fprint_sexp2 s2e in
*)
	let p3t0 = pat2_con_tr_up loc0 freeknd d2c s2vss s2pss s2e npf p2ts in
	let () = if freeknd <> 0 then pat3_confree_tr p3t0 in
	  p3t0

    | PT2empty -> pat3_empty loc0
    | PT2exi (s2vs, p2t) -> pat2_exi_tr_up loc0 s2vs p2t
    | PT2int i -> pat3_int loc0 (sexp2_int_int_t0ype i) i
    | PT2list _ -> error_of_deadcode "ats_trans3: pat2_tr_up: PT2list"
    | PT2lst p2ts ->
	let s2e_elt = SEnv3.sexp2_VarApp_new loc0 srt2_type in
	let s2e_lst =
	  sexp2_list_t0ype_int_type s2e_elt (List.length p2ts) in
	let p3ts = List.map (function p2t -> pat2_tr_dn p2t s2e_elt) p2ts in
	  pat3_lst loc0 s2e_lst p3ts
    | PT2rec (is_flat, is_omit, (npf, lp2ts)) ->
	if not (is_omit) then
	  let lp3ts = labpat2_list_tr_up lp2ts in
	  let ls2es =
	    List.map (function (l, p3t) -> (l, p3t.pat3_type)) lp3ts in
	  let k = tyrec_kind_of_flatness is_flat in
	  let s2e = sexp2_tyrec k npf ls2es in
	    pat3_rec loc0 s2e is_flat npf lp3ts
	else begin
	  P.eprintf "%a: pat2_tr_up: PT2rec: partial record\n"
	    Loc.fprint loc0;
	  Err.abort ();
	end
    | PT2string s ->
	let s2e = sexp2_string_int_type s in pat3_string loc0 s2e s
    | PT2var (isref, d2v, op2t) -> pat2_var_tr_up loc0 isref d2v op2t
    | PT2vbox d2v ->
	let s2e0 =
	  let s2e = d2v.dvar2_master_type in
	    if sexp2_is_empty s2e then
	      let s2e_new = SEnv3.sexp2_VarApp_new loc0 srt2_view in
		(d2v.dvar2_master_type <- s2e_new; s2e_new)
	    else s2e in
	let p3t = pat3_vbox loc0 s2e0 d2v in
	let () = d2v.dvar2_linear <- 0 in
	let () = d2v.dvar2_is_proof <- true in
	let s2e = SEnv3.sexp2_open_and_add s2e0 in
	let () = d2v.dvar2_type <- Some s2e in p3t
(* end of [pat2_tr_up] *)

and pat2_list_tr_up (p2ts: pat2 list): pat3 list =
  List.map pat2_tr_up p2ts

and labpat2_list_tr_up (lp2ts: labpat2 list): labpat3 list =
  List.map (function (l, p2t) -> (l, pat2_tr_up p2t)) lp2ts

and pat2_con_tr_up loc0 (freeknd: int)
  (d2c: dcon2) (s2vss: svar2 list list) (s2pss: sexp2 list list)
  (s2e_fun: sexp2) (npf: int) (p2ts: pat2 list): pat3 =
(*
  let () =
    P.fprintf stdout "pat2_con_tr_up: s2vss = (%a)\n"
      fprint_svar2_list_list s2vss in
*)
  let () = List.iter SEnv3.svar_list_add s2vss in
  let () = List.iter SEnv3.hypo_prop_list_add s2pss in
    match s2e_fun.sexp2_node with
      | SE2fun (
	  _(*lin*), _(*sf2e*), (npf_fun, s2es_fun_arg), s2e_fun_res
	) -> begin
	  let () = SOL.pfarity_equal_solve loc0 npf npf_fun in
	  let p3ts = pat2_list_tr_dn loc0 p2ts s2es_fun_arg in
	    pat3_con loc0 s2e_fun_res freeknd d2c npf p3ts
	end
      | _ -> error_of_deadcode "ats_trans3: pat2_con_tr_up"
(* end of [pat2_con_tr_up] *)

(* ****** ****** *)

and pat2_exi_tr_up
  loc0 (s2vs0: svar2 list) (p2t0: pat2): pat3 = begin
  P.eprintf "%a: pat2_exi_tr_up: not supported.\n" Loc.fprint loc0;
  Err.abort ()
end (* end of [pat2_exi_tr_up] *)

(* ****** ****** *)

and pat2_var_tr_up loc0
  (isref: bool) (d2v: dvar2) (op2t: pat2 option): pat3 = begin
  match op2t with
    | Some p2t ->
	let p3t = pat2_tr_up p2t in
	let s2e = p3t.pat3_type in
	let () = d2v.dvar2_master_type <- s2e in
        let () = if sexp2_is_linear s2e then d2v.dvar2_linear <- 0 in
        let () = if sexp2_is_proof s2e then d2v.dvar2_is_proof <- true in
	let s2e = SEnv3.sexp2_open_and_add s2e in
	let () = d2v.dvar2_type <- Some s2e in
	  pat3_var loc0 s2e isref d2v (Some p3t)
    | None ->
        let s2e0 =
          let s2e = d2v.dvar2_master_type in
            if sexp2_is_empty s2e then
              let s2e_new = SEnv3.sexp2_VarApp_new loc0 srt2_t0ype in
                (d2v.dvar2_master_type <- s2e_new; s2e_new)
            else s2e in
        let p3t = pat3_var loc0 s2e0 isref d2v None in
        let () = if sexp2_is_linear s2e0 then d2v.dvar2_linear <- 0 in
        let () = if sexp2_is_proof s2e0 then d2v.dvar2_is_proof <- true in
        let s2e = SEnv3.sexp2_open_and_add s2e0 in
        let () = d2v.dvar2_type <- Some s2e in p3t
end (* end of [pat2_var_tr_up] *)

(* ****** ****** *)

and pat2_tr_dn (p2t0: pat2) (s2e0: sexp2): pat3 =
  let loc0 = p2t0.pat2_loc in match p2t0.pat2_node with
    | PT2ann (p2t, s2e_ann) ->
	let () = SOL.sexp2_tyleq_solve loc0 s2e0 s2e_ann in
	let p3t = pat2_tr_dn p2t s2e0 in
	let () = p3t.pat3_type <- s2e_ann in p3t

    | PT2any -> pat2_any_tr_dn loc0 s2e0

    | PT2bool b -> pat2_bool_tr_dn loc0 b s2e0
	
    | PT2char c -> pat2_char_tr_dn loc0 c s2e0

    | PT2con (freeknd, d2c, s2vss_d2c, s2pss_d2c, s2e_d2c, np2ts_d2c) ->
	begin match s2e0.sexp2_node with
	  | SE2datuni (d2c1, s2es) ->
(*
	      P.fprintf stdout "pat2_tr_dn: PT2con: s2e0 = %a\n" fprint_sexp2 s2e0;
*)
	      if dcon2_eq d2c d2c1 then pat2_conuni_tr_dn p2t0 s2e0 s2es
	      else begin
		P.eprintf "%a: pat2_tr_dn: PT2con: S2Edatuni: constructor mismatch.\n"
		  Loc.fprint loc0;
		Err.abort ()
	      end
	  | _ -> pat2_con_tr_dn p2t0 s2e0
	end

    | PT2empty ->
	let s2e = SEnv3.sexp2_open_and_add s2e0 in
	let () =
	  SOL.sexp2_equal_solve loc0 s2e (sexp2_void_t0ype ()) in
	  pat3_empty loc0

    | PT2exi (s2vs, p2t) -> pat2_exi_tr_dn loc0 s2vs p2t s2e0

    | PT2int i -> pat2_int_tr_dn loc0 i s2e0

    | PT2lst p2ts ->
	let s2c_d2c = List_t0ype_int_type.make_cst () in
	let s2e_lst = pat2_con_tr_dn_aux loc0 s2c_d2c s2e0 in
	let (s2e_elt, s2i_len) =
	  match un_sexp2_list_t0ype_int_type s2e_lst with
	    | Some (s2e, s2i) -> (s2e, s2i)
	    | None -> error_of_deadcode "ats_trans3: pat2_tr_dn: PT2lst" in
	let p3ts =
	  List.map (function p2t -> pat2_tr_dn p2t s2e_elt) p2ts in
	let () = 
	  SOL.sexp2_hyeq_solve loc0 (sexp2_int (List.length p2ts)) s2i_len in
	let p3t = pat3_lst loc0 s2e_lst p3ts in
	let () = p3t.pat3_type <- s2e0 in p3t

    | PT2rec (is_flat1, is_omit1, (npf, lp2ts)) ->
	pat2_rec_tr_dn loc0 is_flat1 is_omit1 npf lp2ts s2e0

    | PT2string s -> pat2_string_tr_dn loc0 s s2e0

    | PT2var (isref, d2v, op2t) -> pat2_var_tr_dn loc0 isref d2v s2e0 op2t

    | PT2vbox d2v -> begin
	let () = SEnv3.effenv_check_ref loc0  in
	let () = SEnv3.effenv_add_eff Syn.EFFref in
	let s2e0 = sexp2_whnf s2e0 in
	  match un_sexp2_vbox_view_prop s2e0 with
	    | Some s2e ->
(*
		let () =
		  P.fprintf stdout "pat2_tr_dn: PT2vbox: d2v = %a\n"
		    fprint_dvar2 d2v in
		let () =
		  P.fprintf stdout "pat2_tr_dn: PT2vbox: s2e = %a\n"
		    fprint_sexp2 s2e in
*)
		let () = d2v.dvar2_linear <- 0 in
		let () = d2v.dvar2_final <- DVFSvbox s2e in
		let () = d2v.dvar2_master_type <- s2e in
		let s2e = SEnv3.sexp2_open_and_add s2e in
		let () = d2v.dvar2_type <- Some s2e in
		  pat3_vbox loc0 s2e0 d2v
	    | None -> begin
		P.eprintf "%a: pat2_tr_dn: PT2vbox: %a\n"
		  Loc.fprint loc0 fprint_sexp2 s2e0;
		Err.abort ();
	      end
      end

    | _ -> begin
	P.eprintf "%a: pat2_tr_dn:\n" Loc.fprint loc0;
	P.eprintf "  p2t = %a\n" fprint_pat2 p2t0;
	P.eprintf "  s2e = %a\n" fprint_sexp2 s2e0;
	Err.abort ();	
      end
(* end of [pat2_tr_dn] *)

and pat2_list_tr_dn loc0 p2ts0 s2es0: pat3 list =
  let rec aux p2ts s2es = match p2ts, s2es with
    | p2t :: p2ts, s2e :: s2es ->
	let p3t = pat2_tr_dn p2t s2e in p3t :: aux p2ts s2es
    | [], [] -> []
    | [], _ -> EM3.arity_errmsg loc0 (-1)
    | _, [] -> EM3.arity_errmsg loc0 ( 1) in
    aux p2ts0 s2es0
(* end of [pat2_list_tr_dn] *)

and labpat2_list_tr_dn loc0
  (lp2ts0: labpat2 list) (ls2es0: labsexp2 list): labpat3 list =
  let rec aux1 res = function
    | (l, s2e) :: ls2es ->
      let p3t = pat2_any_tr_dn loc0 s2e in aux1 ((l, p3t) :: res) ls2es
    | _ -> List.rev res in
  let rec aux2 res lp2ts0 ls2es0 = match lp2ts0 with
    | [] -> aux1 res ls2es0
    | (l1, p2t) :: lp2ts -> begin match ls2es0 with
	| (l2, s2e) :: ls2es -> begin match Lab.compare l1 l2 with
	  | 0 -> begin
	      let p3t = pat2_tr_dn p2t s2e in
		aux2 ((l1, p3t) :: res) lp2ts ls2es
	    end
	  | 1 -> begin
	      let p3t = pat2_any_tr_dn loc0 s2e in
		aux2 ((l2, p3t) :: res) lp2ts0 ls2es
	    end
	  | _ -> begin
	      P.eprintf "%a: labpat2_list_tr_dn: unrecognized label: <%a>."
		Loc.fprint loc0 Lab.fprint l1;
	      Err.abort ();
	    end
	  end
	| [] -> begin
	    P.eprintf "%a: labpat2_list_tr_dn: too many dynamic expressions.\n"
	      Loc.fprint loc0;
	    Err.abort ();
	  end
      end in
    aux2 [] lp2ts0 ls2es0
(* end of [labpat2_list_tr_dn] *)

(* ****** ****** *)

and pat2_any_tr_dn loc0 (s2e0: sexp2): pat3 =
  let s2e0 = sexp2_whnf s2e0 in
  let d2v = dvar2_new_any loc0 in
  let () = DEnv3.dvar2_add_local d2v in 
  let () = d2v.dvar2_master_type <- s2e0 in
  let () =
    if sexp2_is_linear s2e0 then d2v.dvar2_linear <- 0 in
  let () =
    if sexp2_is_proof s2e0 then d2v.dvar2_is_proof <- true in
  let () =
    let s2e = SEnv3.sexp2_open_and_add s2e0 in
      d2v.dvar2_type <- Some s2e in
    pat3_any loc0 s2e0 d2v
(* end of [pat2_any_tr_dn] *)

(* ****** ****** *)

and pat2_assert_tr_dn loc0 (s2e0: sexp2): unit =
  let _ (* p3t *) = pat2_bool_tr_dn loc0 true s2e0 in ()

and pat2_bool_tr_dn loc0 (b: bool) (s2e0: sexp2): pat3 =
  let s2e =
    let s2c = Bool_bool_t0ype.make_cst () in
      pat2_con_tr_dn_aux loc0 s2c s2e0 in
  let os2c =
    let s2e_head = sexp2_head s2e in
      match s2e_head.sexp2_node with
	| SE2cst s2c -> Some s2c | _ -> None in
  let p3t =
    match os2c with
      | Some s2c when Bool_t0ype.eq_cst s2c -> pat3_bool loc0 s2e b
      | Some s2c when Bool_bool_t0ype.eq_cst s2c ->
	  let s2e_bool = sexp2_bool_bool_t0ype b in
	  let () = SOL.sexp2_hyeq_solve loc0 s2e s2e_bool in
	    pat3_bool loc0 s2e_bool b
      | _ -> begin
	  P.eprintf "%a: boolean type is expected: %a\n"
	    Loc.fprint loc0 fprint_sexp2 s2e0;
	  Err.abort ();
	end in
  let () = p3t.pat3_type <- s2e0 in p3t
(* end of [pat2_bool_tr_dn] *)

(* ****** ****** *)

and pat2_char_tr_dn loc0 (c: char) (s2e0: sexp2): pat3 =
  let s2e =
    let s2c = Char_char_t0ype.make_cst () in
      pat2_con_tr_dn_aux loc0 s2c s2e0 in
  let os2c =
    let s2e_head = sexp2_head s2e in
      match s2e_head.sexp2_node with
	| SE2cst s2c -> Some s2c | _ -> None in
  let p3t = match os2c with
    | Some s2c when Char_t0ype.eq_cst s2c -> pat3_char loc0 s2e c
    | Some s2c when Char_char_t0ype.eq_cst s2c ->
	let s2e_char = sexp2_char_char_t0ype c in
	let () = SOL.sexp2_hyeq_solve loc0 s2e s2e_char in
	  pat3_char loc0 s2e_char c
    | _ -> begin
	P.eprintf "%a: character type is expected: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e0;
	Err.abort ();
      end in
  let () = p3t.pat3_type <- s2e0 in p3t
(* end of [pat2_char_tr_dn] *)

(* ****** ****** *)

and pat2_con_tr_dn_aux loc0 (s2c0: scst2) (s2e0: sexp2): sexp2 =
(*
  let () =
    P.fprintf stdout "pat2_con_tr_dn_aux: s2e0 = %a\n"
      fprint_sexp2 s2e0 in
*)
  let s2e0 = SEnv3.sexp2_open_and_add s2e0 in
  let s2e1 = match s2e0.sexp2_node with
    | SE2Var s2V -> begin match un_srt2_fun s2c0.scst2_sort with
	| None -> sexp2_cst s2c0
	| Some (s2ts, _) ->
	    let stamps = s2V.sVar2_svs in
	    let s2es_arg =
	      List.map
		(function s2t ->
		   SEnv3.sexp2_Var_new_with_stamps loc0 s2t stamps)
		s2ts in
	    let s2e = sexp2_cstapp s2c0 s2es_arg in
	      (s2V.sVar2_link <- Some s2e; s2e)
      end
    | SE2VarApp (s2V, arg) ->
	let (s2v, s2c_args) =
	  SEnv3.scst2_closure loc0 s2V.sVar2_svs s2c0 in
	let s2t_res = s2e0.sexp2_sort in
	let s2e_body =
	  sexp2_app_with_sort s2t_res (sexp2_cst s2c0) s2c_args in
	let s2t_arg = s2v.svar2_sort in
	let () = srt2_solve s2V.sVar2_arg_sort s2t_arg in
	let s2t_fun = srt2_fun [s2t_arg] s2t_res in
	let s2e_lam = sexp2_lam_with_sort s2t_fun [s2v] s2e_body in
	let () =
	  if not (sexp2_occurs s2V s2e_lam) then
	    SEnv3.sVar2_assign_with_error loc0 s2V s2e_lam
	  else EM3.occur_check_errmsg loc0 s2V s2e_lam
	in sexp2_subst [(s2v, arg)] s2e_body
    | _ -> s2e0 in
  let () = 
    let s2e1_head = sexp2_head s2e1 in match s2e1_head.sexp2_node with
      | SE2cst s2c1 ->
	  if not (scst2_leq s2c0 s2c1) then begin
	    P.eprintf "%a: pat2_con_tr_dn_aux: %a <> %a\n"
	      Loc.fprint loc0 fprint_scst2 s2c0 fprint_scst2 s2c1;
	    Err.abort ();
	  end
      | _ -> begin
	  P.eprintf "%a: pat2_con_tr_dn_aux: illegal pattern: %a : %a\n"
	    Loc.fprint loc0 fprint_scst2 s2c0 fprint_sexp2 s2e1;
	  Err.abort ();
	end in
    s2e1
(* end of [pat2_con_tr_dn_aux] *)

(* ****** ****** *)

and pat2_con_tr_dn (p2t0: pat2) (s2e0: sexp2): pat3 = begin
  let loc0 = p2t0.pat2_loc in match p2t0.pat2_node with
    | PT2con (freeknd, d2c, s2vss_d2c, s2pss_d2c, s2e_d2c, np2ts_d2c) ->
	let freeknd =
	  if d2c.dcon2_vwtp then freeknd else 0 in
	let s2c_d2c = d2c.dcon2_scst in
	let s2e_res = pat2_con_tr_dn_aux loc0 s2c_d2c s2e0 in
	let (npf_d2c, p2ts_d2c) = np2ts_d2c in
	let p3t0 = match s2e_d2c.sexp2_node with
	  | SE2fun (
	      _(*lin*), _(*sf2e*), (npf_fun, s2es_fun_arg), s2e_fun_res
	    ) -> begin
	      let () = SOL.pfarity_equal_solve loc0 npf_d2c npf_fun in
	      let () = List.iter SEnv3.svar_list_add s2vss_d2c in
	      let () = List.iter SEnv3.hypo_prop_list_add s2pss_d2c in
(*
	      let () =
		P.fprintf stdout "pat2_tr_dn: PT2con: s2e_fun_res = %a\n"
		  fprint_sexp2 s2e_fun_res in
	      let () =
		P.fprintf stdout "pat2_tr_dn: PT2con: s2e_res = %a\n"
		  fprint_sexp2 s2e_res in
*)
	      let () = SOL.sexp2_hyeq_solve loc0 s2e_fun_res s2e_res in
	      let p3ts_d2c = pat2_list_tr_dn loc0 p2ts_d2c s2es_fun_arg in
		pat3_con loc0 s2e_res freeknd d2c npf_d2c p3ts_d2c
	    end
	  | _ -> error_of_deadcode "ats_trans3: pat2_con_tr_dn" in

	let () = p3t0.pat3_type <- s2e0 in
	let () = if freeknd <> 0 then pat3_confree_tr p3t0 in
	  p3t0
    | _ -> begin
	error_of_deadcode "ats_trans3: pat2_con_tr_dn"
      end
end (* end of pat2_con_tr_dn *)

(* ****** ****** *)

and pat2_conuni_tr_dn
  (p2t0: pat2) (s2e0: sexp2) (s2es_uni: sexp2 list): pat3 = begin
  let loc0 = p2t0.pat2_loc in match p2t0.pat2_node with
    | PT2con (freeknd, d2c, s2vss_d2c, s2pss_d2c, s2e_d2c, np2ts_d2c) ->
	let (npf_d2c, p2ts_d2c) = np2ts_d2c in
	let () = List.iter SEnv3.svar_list_add s2vss_d2c in
	let p3ts_d2c = pat2_list_tr_dn loc0 p2ts_d2c s2es_uni in
	let p3t0 = pat3_con loc0 s2e0 freeknd d2c npf_d2c p3ts_d2c in
	let () = pat3_confree_tr p3t0 in
	  p3t0
    | _ -> begin
	error_of_deadcode "ats_trans3: pat2_conuni_tr_dn"
      end
end (* end of pat2_conuni_tr_dn *)

(* ****** ****** *)

and pat2_exi_tr_dn loc0
  (s2vs0: svar2 list) (p2t0: pat2) (s2e0: sexp2): pat3 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2exi (s2vs, s2ps, s2e) ->
	let () = SEnv3.svar_list_add s2vs0 in
	let sub = svar2_list_bind loc0 s2vs s2vs0 in
	let () = SEnv3.hypo_prop_list_add (sexp2_list_subst sub s2ps) in
	let p3t0 = pat2_tr_dn p2t0 (sexp2_subst sub s2e) in
	let () = p3t0.pat3_type <- s2e0 in p3t0
    | _ -> begin
	P.eprintf
	  "%a: pat2_exi_tr_dn: not an existentially quantified type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e0;
	Err.abort ();
      end
(* end of [pat2_exi_tr_dn] *)

(* ****** ****** *)

and pat2_int_tr_dn loc0 (i: intinf) (s2e0: sexp2): pat3 =
  let s2e =
    let s2c = Int_int_t0ype.make_cst () in
      pat2_con_tr_dn_aux loc0 s2c s2e0 in
  let os2c =
    let s2e_head = sexp2_head s2e in
      match s2e_head.sexp2_node with
	| SE2cst s2c -> Some s2c | _ -> None in
(*
  let () =
    P.fprintf stdout "pat2_int_tr_dn: s2e = %a\n" fprint_sexp2 s2e in
  let () =
    P.fprintf stdout "pat2_int_tr_dn: i = %i\n" i in
*)
  let p3t = match os2c with
    | Some s2c when Int_t0ype.eq_cst s2c -> pat3_int loc0 s2e i
    | Some s2c when Int_int_t0ype.eq_cst s2c ->
	let s2e_int = sexp2_int_int_t0ype i in
	let () = SOL.sexp2_hyeq_solve loc0 s2e s2e_int in
	  pat3_int loc0 s2e_int i
    | Some s2c when Uint_t0ype.eq_cst s2c -> pat3_int loc0 s2e i
    | Some s2c when Uint_int_t0ype.eq_cst s2c ->
	let s2e_uint = sexp2_uint_int_t0ype i in
	let () = SOL.sexp2_hyeq_solve loc0 s2e s2e_uint in
	  pat3_int loc0 s2e_uint i
    | _ -> begin
	P.eprintf "%a: an integer type is expected: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end in
  let () = p3t.pat3_type <- s2e0 in p3t
(* end of [pat2_int_tr_dn] *)

(* ****** ****** *)

and pat2_rec_tr_dn loc0
  (is_flat1: bool) (is_omit1: bool)
  (npf1: int) (lp2ts: labpat2 list) (s2e0: sexp2): pat3 =
  let s2e = SEnv3.sexp2_open_and_add s2e0 in
  let p3t = match s2e.sexp2_node with
    | SE2tyrec (k, (npf, ls2es)) ->
	let () = match is_flat1 with
	  | true -> begin match k with
	      | TYRECflt _ -> () | _ -> EM3.flatness_errmsg loc0 k
	    end
	  | false -> begin match k with
	      | TYRECflt _ -> EM3.flatness_errmsg loc0 k | _ -> ()
	    end in
	let () = if npf1 <> npf then EM3.pfarity_errmsg loc0 in
	let lp3ts = labpat2_list_tr_dn loc0 lp2ts ls2es in
	  pat3_rec loc0 s2e0 is_flat1 npf1 lp3ts
    | _ -> begin match is_omit1 with
	| false ->
	    let lp3ts =
	      List.map (function (l, p2t) -> (l, pat2_tr_up p2t)) lp2ts in
	    let ls2es =
	      List.map (function (l, p3t) -> (l, p3t.pat3_type)) lp3ts in
	    let k = tyrec_kind_of_flatness is_flat1 in
	    let s2e_rec = sexp2_tyrec k npf1 ls2es in
	    let () = SOL.sexp2_equal_solve loc0 s2e_rec s2e in
	      pat3_rec loc0 s2e is_flat1 npf1 lp3ts
	| true -> begin
	    P.eprintf "%a: pat2_rec_tr_dn: partial records.\n"
	      Loc.fprint loc0;
	    Err.abort ();
	  end
      end in
  let () = p3t.pat3_type <- s2e0 in p3t
(* end of [pat2_rec_tr_dn] *)

(* ****** ****** *)

and pat2_string_tr_dn loc0 (s: string) (s2e0: sexp2): pat3 =
  let s2e =
    let s2c = String_int_type.make_cst () in
      pat2_con_tr_dn_aux loc0 s2c s2e0 in
  let os2c =
    let s2e_head = sexp2_head s2e in
      match s2e_head.sexp2_node with
	| SE2cst s2c -> Some s2c | _ -> None in
  let p3t = match os2c with
    | Some s2c when String_type.eq_cst s2c -> pat3_string loc0 s2e s
    | Some s2c when String_int_type.eq_cst s2c ->
	let s2e_str = sexp2_string_int_type s in
	let () = SOL.sexp2_hyeq_solve loc0 s2e s2e_str in
	  pat3_string loc0 s2e_str s
    | _ -> begin
	P.eprintf "%a: string type is expected: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e0;
	Err.abort ();
      end in
  let () = p3t.pat3_type <- s2e0 in p3t
(* end of [pat2_string_tr_dn] *)

(* ****** ****** *)

and pat2_var_tr_dn loc0
  (isref: bool) (d2v: dvar2) (s2e0: sexp2) (op2t: pat2 option): pat3 =
  let s2e0 = sexp2_whnf s2e0 in
  let () = d2v.dvar2_master_type <- s2e0 in
  let () = if sexp2_is_linear s2e0 then d2v.dvar2_linear <- 0 in
  let () = if sexp2_is_proof s2e0 then d2v.dvar2_is_proof <- true in
  let op3t = match op2t with
    | Some p2t -> begin
	let () =
	  if not (isref) && sexp2_is_linear s2e0 then begin
	    P.eprintf "%a: pat2_var_tr_dn: linear [as] pattern is not allowed.\n"
	      Loc.fprint loc0;
	    Err.abort ();
	  end in
	let p3t = pat2_tr_dn p2t s2e0 in
	  (d2v.dvar2_type <- Some (p3t.pat3_type); Some p3t)
      end
    | None -> begin
	let s2e = SEnv3.sexp2_open_and_add s2e0 in
	  (d2v.dvar2_type <- Some s2e; None)
      end in
  let p3t0 = pat3_var loc0 s2e0 isref d2v op3t in
(*
  let () =
    P.fprintf stdout "pat2_tr_dn: PT2var:\n" in
  let () =
    P.fprintf stdout "  d2v = %a\n" fprint_dvar2 d2v in
  let () =
    P.fprintf stdout "  s2e0 = %a\n" fprint_sexp2 s2e0 in
  let () =
    P.fprintf stdout "  s2t0 = %a\n" fprint_srt2 s2e0.sexp2_sort in
*)
    p3t0
(* end of [pat2_var_tr_dn] *)

(* ****** ****** *)

let rec pat2_arg_tr_up (p2t0: pat2): pat3 =
  match p2t0.pat2_type with
    | Some s2e -> pat2_tr_dn p2t0 s2e
    | None -> begin match p2t0.pat2_node with
	| PT2ann (p2t, s2e) -> pat2_arg_tr_dn p2t s2e
	| _ -> pat2_tr_up p2t0
      end
(* end of [pat2_arg_tr_up] *)

and pat2_arg_list_tr_up (npf: int) (p2ts0: pat2 list): pat3 list =
  let rec aux i p2ts = match p2ts with
    | p2t :: p2ts ->
	let () = if i < npf then pat2_proofize p2t in
	let p3t = pat2_arg_tr_up p2t in p3t :: aux (i+1) p2ts
    | [] -> [] in
    aux 0 p2ts0
(* end of [pat2_arg_list_tr_up] *)

and pat2_arg_tr_dn (p2t0: pat2) (s2e0: sexp2): pat3 =
  let s2e0 = sexp2_whnf s2e0 in
  let refval_arg_res_opt = match s2e0.sexp2_node with
    | SE2refarg (refval, s2e_arg, s2e_res) -> Some (refval, s2e_arg, s2e_res)
    | _ -> None in
    begin match refval_arg_res_opt with
      | Some (refval, s2e_arg, s2e_res) -> begin
(*
	let () =
	  P.fprintf stdout
	    "pat2_arg_tr_dn: p2t0 = %a\n" fprint_pat2 p2t0 in
	let () =
	  P.fprintf stdout
            "pat2_arg_tr_dn: s2e_arg = %a\n" fprint_sexp2 s2e_arg in
	let () =
	  P.fprintf stdout
            "pat2_arg_tr_dn: s2e_res = %a\n" fprint_sexp2 s2e_res in
*)
	let loc0 = p2t0.pat2_loc in match p2t0.pat2_node with
	  | PT2var (isref, d2v, op2t) -> begin
	      let isprf =
		if refval = 0 then true else sexp2_is_proof s2e_arg in
              match isprf with
	      | true -> begin
		  let p3t0 =
		    pat2_var_tr_dn loc0 isref d2v s2e_arg op2t in
		  let () = match op2t with
		    | Some _ -> d2v.dvar2_type <- None | None -> () in
		  let () = d2v.dvar2_master_type <- s2e_res in
		  let () = d2v.dvar2_final <- DVFSsome s2e_res in
		    (p3t0.pat3_type <- s2e0; p3t0)
		end
	      | false -> begin
		  let op3t = match op2t with
		    | Some p2t -> Some (pat2_tr_dn p2t s2e_arg) | None -> None in
		  let s2e_arg_new = match op3t with
		    | Some p3t -> p3t.pat3_type
		    | None -> begin
			SEnv3.sexp2_open_and_add s2e_arg
		      end in
		  let s2v_addr =
		    svar2_new_with_id
		      (Syn.sid_of_did d2v.dvar2_name) srt2_addr in
		  let s2e_addr = sexp2_var s2v_addr in
		  let () = SEnv3.svar_add s2v_addr in
		  let () = d2v.dvar2_addr <- Some s2e_addr in
		  let () = SEnv3.hypo_prop_add (sexp2_pgt_null s2e_addr) in
		  let d2v_view = DEnv3.dvar2_ptr_viewat_make d2v in
                  let () = d2v.dvar2_view <- Some d2v_view in (* [d2v] is mutable *)
		  let () =
		    let s2e =
		      sexp2_at_viewt0ype_addr_view s2e_res s2e_addr in
		      d2v_view.dvar2_master_type <- s2e in
		  let () =
		    let s2e = match op3t with
		      | Some p3t -> begin
			  if sexp2_is_linear s2e_arg_new then
			    match p3t.pat3_type_left with
			      | Some s2e -> s2e | None -> sexp2_topize s2e_arg_new
			  else s2e_arg_new
                        end
		      | None -> s2e_arg_new in
		    let s2e_at =
		      sexp2_at_viewt0ype_addr_view s2e s2e_addr in
		      d2v_view.dvar2_type <- Some s2e_at in
		  let () =
		    let s2e = 
		      sexp2_at_viewt0ype_addr_view s2e_res s2e_addr in
		      d2v_view.dvar2_final <- DVFSsome s2e in
		    pat3_var loc0 s2e0 isref d2v op3t
		end
	    end
	  | _ -> begin
	      P.eprintf "%a: pat2_tr_dn_arg: S2Erefarg_w: %a\n"
		Loc.fprint loc0 fprint_sexp2 s2e0;
	      Err.abort ();
	    end
	end
      | _ -> pat2_tr_dn p2t0 s2e0
    end (* end of [pat2_arg_tr_dn] *)
(* end of [pat2_arg_tr_dn] *)

and pat2_arg_list_tr_dn loc0 (npf: int)
  (p2ts0: pat2 list) (s2es0: sexp2 list): pat3 list =
  let rec aux i p2ts s2es = match p2ts, s2es with
    | p2t :: p2ts, s2e :: s2es ->
	let () = if i < npf then pat2_proofize p2t in
	let p3t = pat2_arg_tr_dn p2t s2e in
	  p3t :: aux (i+1) p2ts s2es
    | [], [] -> []
    | _ :: _, [] -> EM3.arity_errmsg loc0 1
    | [], _ :: _ -> EM3.arity_errmsg loc0 0 in
    aux 0 p2ts0 s2es0
(* end of [pat2_arg_list_tr_dn] *)

(* ****** ****** *)

let rec patcst2_tr loc0 (p2tc: patcst2) (s2e: sexp2): unit =
  let s2e = SEnv3.sexp2_open_and_add s2e in match p2tc with
    | PTC2any -> ()
    | PTC2int i ->
	SOL.sexp2_hyeq_solve loc0 s2e (sexp2_int_int_t0ype i)
    | _ -> error_of_unavailability "patcst2_tr: yet to be done"
(* end of [patcst2_tr] *)

and patcst2_list_tr loc0 (p2tcs: patcst2 list) (s2es: sexp2 list): unit =
  let n1 = List.length p2tcs and n2 = List.length s2es in
    match compare n1 n2 with
      | 0 -> List.iter2 (patcst2_tr loc0) p2tcs s2es
      | i -> error "patcst2_list_tr: unequal length"
(* end of [patcst2_list_tr] *)

(* ****** ****** *)

let patcst2_intc_hypo_add (s2i: sexp2) (xs: intinf list): unit =
  List.iter
    (function x ->
       SEnv3.hypo_prop_add (Ineq.make_exp (Some [s2i; sexp2_intinf x]))) xs
(* end of [patcst2_intc_hypo_add] *)

let rec patcst2_hypo_add loc0
  (p2tc: patcst2) (s2e0: sexp2): unit =
  let s2e0 = SEnv3.sexp2_open_and_add s2e0 in match p2tc with
    | PTC2any -> ()
    | PTC2bool b -> begin
	match un_sexp2_bool_bool_t0ype s2e0 with
	  | Some s2b -> SOL.sexp2_hyeq_solve loc0 s2b (sexp2_bool b)
	  | None -> ()
      end
    | PTC2char _ -> ()
    | PTC2con (d2c, p2tcs) -> begin match s2e0.sexp2_node with
	| SE2datuni (d2c1, _) -> begin
	    if dcon2_eq d2c d2c1 then () else SEnv3.hypo_prop_add (sexp2_bool false)
	  end
	| _ -> begin
	    let (s2vss_d2c, s2pss_d2c, s2e_d2c) = Tr2.pat1_con_tr_inst loc0 d2c [] in
	    let (s2es_fun_arg, s2e_fun_res) =
	      match s2e_d2c.sexp2_node with
		| SE2fun (_, _, (npf, s2es), s2e) -> (s2es, s2e)
		| _ -> begin
		    error_of_deadcode "ats_pat_trans3: patcst2_hypo_add"
		  end in
(*
            let () =
              P.fprintf stdout "patcst2_hypo_add: s2vss_d2c = %a\n"
                fprint_svar2_list_list s2vss_d2c in
*)
	    let () = List.iter SEnv3.svar_list_add s2vss_d2c in
	    let () = List.iter SEnv3.hypo_prop_list_add s2pss_d2c in
	    let () = SOL.sexp2_hyeq_solve loc0 s2e_fun_res s2e0 in
	      patcst2_list_hypo_add loc0 p2tcs s2es_fun_arg
	  end
      end (* end of [PTC2con] *)
    | PTC2empty -> ()
    | PTC2int i -> begin match un_sexp2_int_int_t0ype s2e0 with
	| Some s2i -> SOL.sexp2_hyeq_solve loc0 s2i (sexp2_intinf i)
        | None -> ()
      end
    | PTC2intc xs -> begin match un_sexp2_int_int_t0ype s2e0 with
	| Some s2i -> patcst2_intc_hypo_add s2i xs
	| None -> ()
      end
    | PTC2rec lp2tcs -> begin match s2e0.sexp2_node with
	| SE2tyrec (is_flat, (npf, ls2es)) ->
	    labpatcst2_list_hypo_add loc0 lp2tcs ls2es
	| _ -> ()
      end
    | PTC2string _ -> ()
    | PTC2vbox -> ()
(* end of [patcst2_hypo_add] *)

and patcst2_list_hypo_add loc0
  (p2tcs: patcst2 list) (s2es: sexp2 list): unit =
  List.iter2 (patcst2_hypo_add loc0) p2tcs s2es

and labpatcst2_list_hypo_add loc0
  (lp2tcs: labpatcst2 list) (ls2es: labsexp2 list): unit =
(*
  let () =
    P.fprintf stdout "labpatcst2_list_hypo_add: lp2tcs = %a\n"
      fprint_labpatcst2_list lp2tcs in
  let () =
    P.fprintf stdout "labpatcst2_list_hypo_add: ls2es = %a\n"
      fprint_labsexp2_list ls2es in
*)
  let rec aux lp2tcs ls2es = match lp2tcs, ls2es with
    | (l, p2tc) :: lp2tcs1, (l', s2e) :: ls2es1 ->
	if Lab.eq l l' then
	  (patcst2_hypo_add loc0 p2tc s2e; aux lp2tcs1 ls2es1)
	else (aux lp2tcs ls2es1)
    | [], _ -> ()
    | _, [] -> error_of_deadcode "ats_trans3_pat: labpatcst2_list_hypo_add" in
    aux lp2tcs ls2es
(* end of [labpatcst2_list_hypo_add] *)

(* ****** ****** *)

let patcst2_list_list_cstr_add loc0
  (p2tcss: patcst2 list list) (s2es: sexp2 list): unit =
  let aux p2tcs =
    let () = SEnv3.env_push () in
    let () = patcst2_list_hypo_add loc0 p2tcs s2es in
    let s3is = SEnv3.env_pop () in s3is in
  let s3iss = List.map aux p2tcss in SEnv3.disj_add s3iss
(* end of [patcst2_list_list_cstr_add] *)

(* ****** ****** *)

let pattern_match_is_nonexhaustive_check loc0
  (sgn: int) (p2tcss: patcst2 list list) (s2es: sexp2 list): unit =
  let aux p2tcs =
    let () = SEnv3.env_push () in
    let () = patcst2_list_hypo_add loc0 p2tcs s2es in
    let () =
      SEnv3.cstr_nonexhaustive_pattern_match_add loc0 sgn p2tcs in
    let s3is = SEnv3.env_pop () in
      SEnv3.cstr_add (SEnv3.cstr3_itms s3is) in
    List.iter aux p2tcss
(* end of [pattern_match_is_nonexhaustive] *)

(* ****** ****** *)

(* end of [ats_trans3_pat] *)
