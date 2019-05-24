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

open Ats_staexp2
open Ats_staexp2_util
open Ats_stacst2
open Ats_dynexp2
open Ats_dynexp2_util
open Ats_dyncst2
open Ats_misc

module P = Printf

module Err = Ats_error
module Loc = Ats_location
module Lab = Ats_label

module SS = Ats_svar_stamp
module SEnv3 = Ats_staenv3
module SOL = Ats_staexp2_solve

(* some type abbreviations *)

type loc = Loc.location
type lab = Lab.label

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_dynenv3: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

type ldvs_item =
  | LDVSlam
  | LDVSllam of DvarSet.t ref
  | LDVSset of DvarSet.t

let the_local_dvar2set: DvarSet.t ref = ref DvarSet.empty
let the_local_dvar2set_list: (ldvs_item) list ref = ref []

let local_dvar2set_get (): DvarSet.t = !the_local_dvar2set
let local_dvar2set_get_llam (): DvarSet.t =
  match !the_local_dvar2set_list with
    | LDVSllam r :: _ -> !r | _ -> error "local_dvar2set_get_llam"
(* end of [local_dvar2set_get_llam] *)

let dvar2_add_local (d2v: dvar2): unit =
  (the_local_dvar2set := DvarSet.add d2v !the_local_dvar2set)

let dvar2_list_add_local (d2vs: dvar2 list): unit =
  List.iter dvar2_add_local d2vs

let pat2_dvs_add_local (p2t: pat2): unit =
  dvar2_list_add_local p2t.pat2_dvs

(* ****** ****** *)

let dvar2_is_local_lam (d2v: dvar2): bool =
  let rec aux xs = match xs with
    | x :: xs -> begin match x with
	| (LDVSlam | LDVSllam _) -> false
	| LDVSset d2vs -> (DvarSet.mem d2v d2vs || aux xs)
      end
    | [] -> error "dvar2_is_local_lam: aux" in
    if DvarSet.mem d2v !the_local_dvar2set then true
    else aux !the_local_dvar2set_list
(* end of [dvar2_is_local_lam] *)

let dvar2_is_local_llam (d2v: dvar2): bool =
  let rec aux xs = match xs with
    | x :: xs -> begin match x with
	| LDVSlam -> false
	| LDVSllam r -> (r := DvarSet.add d2v !r; aux xs)
	| LDVSset d2vs -> (DvarSet.mem d2v d2vs || aux xs)
      end
    | [] -> error "dvar2_is_local_llam: aux" in
    if DvarSet.mem d2v !the_local_dvar2set then true
    else aux !the_local_dvar2set_list
(* end of [dvar2_is_local_llam] *)

(* ****** ****** *)

let env_push_lam (is_linear: bool): unit =
  let marker =
    if is_linear then LDVSllam (ref DvarSet.empty) else LDVSlam in
    begin
      the_local_dvar2set_list :=
      marker :: LDVSset (!the_local_dvar2set) :: !the_local_dvar2set_list;
      the_local_dvar2set := DvarSet.empty;
    end
(* end of [env_push_lam] *)

let env_pop_lam (): unit =
  match !the_local_dvar2set_list with
    | LDVSlam :: LDVSset d2vs :: rest -> begin
	the_local_dvar2set := d2vs;
	the_local_dvar2set_list := rest;
      end
    | LDVSllam _ :: LDVSset d2vs :: rest -> begin
	the_local_dvar2set := d2vs;
	the_local_dvar2set_list := rest;
      end
    | _ -> error "env_pop_lam"
(* end of [env_pop_lam] *)

let env_push_let (): unit = begin
  the_local_dvar2set_list :=
    LDVSset (!the_local_dvar2set) :: !the_local_dvar2set_list;
  the_local_dvar2set := DvarSet.empty;
end (* end of [env_push_let] *)

let env_pop_let (): unit =
  match !the_local_dvar2set_list with
    | LDVSset d2vs :: rest -> begin
	the_local_dvar2set := d2vs;
	the_local_dvar2set_list := rest;
      end
    | _ -> error "env_pop_let"
(* end of [env_pop_let] *)

let env_push_try (): unit = env_push_lam false
let env_pop_try (): unit = env_pop_lam ()

(* ****** ****** *)

let dvar2_ptr_viewat_make (d2v_ptr: dvar2): dvar2 =
  let loc_ptr = d2v_ptr.dvar2_loc in
  let d2v_view =
    let name =
      P.sprintf "%s.view" (Syn.string_of_did d2v_ptr.dvar2_name) in
    let did = Syn.make_did_with_loc_and_string loc_ptr name in
      dvar2_new_with_id loc_ptr did false (* is_fixed *) in
  let () = d2v_view.dvar2_addr <- d2v_ptr.dvar2_addr in
  let () = dvar2_add_local d2v_view in
  let () = d2v_view.dvar2_linear <- 0 in
  let () = d2v_view.dvar2_is_proof <- true in d2v_view
(* end of [dvar2_ptr_viewat_make] *)

(* ****** ****** *)

exception Exn_dvar2_viewat_find of
  dvar2 * sexp2 (* type *) * sexp2 (* addr *) * slab2 list * slab2 list

let dvar2_viewat_find (s2r0: sexp2) (s2labs0: slab2 list)
  : (dvar2 * sexp2 * sexp2 * slab2 list * slab2 list) option =
  let f (d2v: dvar2): unit = match d2v.dvar2_type with
    | Some s2e -> begin let s2e = sexp2_whnf s2e in
	match un_sexp2_at_viewt0ype_addr_view s2e with
	  | Some (s2e_elt, s2l) -> begin
	      let (s2r, s2labs_ft) = sexp2_addr_norm s2l in
		if sexp2_syneq s2r0 s2r then begin
		  match slab2_list_is_prefix s2labs_ft s2labs0 with
		    | Some s2labs_bk -> raise
			(Exn_dvar2_viewat_find
                           (d2v, s2e_elt, s2l, s2labs_ft, s2labs_bk))
		    | None -> ()
		end
	    end
	  | None -> ()
      end (* end of [let] *)
    | None -> () in
  let rec aux xs = match xs with
    | x :: xs -> begin match x with
	| LDVSlam -> None
	| LDVSllam _ -> aux xs
	| LDVSset d2vs -> (DvarSet.iter f d2vs; aux xs)
      end
    | [] -> None in
    try begin
      DvarSet.iter f !the_local_dvar2set;
      aux !the_local_dvar2set_list
    end with Exn_dvar2_viewat_find (d2v, s2e_elt, s2l, s2labs_ft, s2labs_bk) ->
      Some (d2v, s2e_elt, s2l, s2labs_ft, s2labs_bk)
(* end of [dvar2_viewat_find] *)

(* ****** ****** *)

let dynenv_final_check (loc0: loc): unit =
  let aux (d2v: dvar2) =
    if dvar2_is_linear d2v then begin
      match d2v.dvar2_type with
	| None -> begin match d2v.dvar2_final with
	    | DVFSnone -> ()
	    | _ -> begin
		P.fprintf stderr
		  "%a: dynenv_final_check: not preserved variable: <%a>\n"
		  Loc.fprint loc0 fprint_dvar2 d2v;
		Err.abort ();
	      end
	  end
	| Some s2e -> begin match d2v.dvar2_final with
	    | DVFSsome s2e0 ->
(*
		let () =
		  P.fprintf stdout "dynenv_final_check: d2v = %a\n" fprint_dvar2 d2v in
		let () =
		  P.fprintf stdout "dynenv_final_check: s2e = %a\n" fprint_sexp2 s2e in
		let () =
		  P.fprintf stdout "dynenv_final_check: s2e0 = %a\n" fprint_sexp2 s2e0 in
*)
		let () = SOL.sexp2_tyleq_solve loc0 s2e s2e0 in
		  d2v.dvar2_type <- Some s2e0
	    | DVFSvbox s2e0 ->
		let () = SOL.sexp2_tyleq_solve loc0 s2e s2e0 in
		  d2v.dvar2_type <- Some s2e0
	    | DVFSnone ->
		if sexp2_is_nonlin s2e then (d2v.dvar2_type <- None)
		else begin
		  P.fprintf stderr
		    "%a: dynenv_final_check: not consumed variable: %a: %a\n"
		    Loc.fprint loc0 fprint_dvar2 d2v fprint_sexp2 s2e;
		  Err.abort ();
		end
	  end
    end in DvarSet.iter aux (local_dvar2set_get ())
(* end of [dynenv_final_check] *)

let dynenv_final_check_llam (loc0: loc): unit =
  let aux (d2v: dvar2) = match d2v.dvar2_type with
    | None -> ()
    | Some s2e ->
	if sexp2_is_nonlin s2e then d2v.dvar2_type <- None
	else begin
	  P.fprintf stderr
	    "%a: dynenv_final_check_llam: not consumed variable: %a: %a\n"
	    Loc.fprint loc0 fprint_dvar2 d2v fprint_sexp2 s2e;
	  Err.abort ();
	end in
    DvarSet.iter aux (local_dvar2set_get_llam ())
(* end of [dynenv_final_check_llam] *)

(* ****** ****** *)

type state_before_item = {
  sbi_dvar : dvar2;
  sbi_type_opt : sexp2 option;
  sbi_lin : int;
}

type state_before = state_before_item list

(* ****** ****** *)

let state_check_with_before loc0 (sty: statype2)
  (inv_met: sexp2 list option) (sbis: state_before): unit =
  let sub =
    SEnv3.sexp2_inst_and_add loc0 sty.statype2_svs sty.statype2_gua in
  let () = match sty.statype2_met, inv_met with
    | Some metric, Some metric_bound ->
(*
	let () =
	  P.fprintf stdout
	    "state_check_with_before: metric = %a\n"
	    fprint_sexp2_list metric in
	let () =
	  P.fprintf stdout
	    "state_check_with_before: metric_bound = %a\n"
	    fprint_sexp2_list metric_bound in
*)
	SEnv3.metric_add loc0 (sexp2_list_subst sub metric) metric_bound
    | _, _ -> () in
  let aux sbi =
    let d2v = sbi.sbi_dvar in match statype2_dvar2_assoc sty d2v with
      | Some s2e -> begin match d2v.dvar2_type with
	  | Some s2e_dvar ->
	      let s2e_check = sexp2_subst sub s2e in
		SOL.sexp2_tyleq_solve loc0 s2e_dvar s2e_check
	  | None -> begin
	      P.fprintf stderr
		"%a: state_check_with_before: not preserved variable: %a\n"
		Loc.fprint loc0 fprint_dvar2 d2v
	    end
	end
      | None -> begin
	  if d2v.dvar2_linear > sbi.sbi_lin then
	    match d2v.dvar2_type, sbi.sbi_type_opt with
	      | None, None -> ()
	      | Some s2e_dvar, Some s2e_check ->
		  SOL.sexp2_tyleq_solve loc0 s2e_dvar s2e_check
	      | None, Some _ -> begin
		  P.fprintf stderr
		    "%a: state_check_with_before: not preserved variable: %a\n"
		    Loc.fprint loc0 fprint_dvar2 d2v
		end
	      | Some _, None -> begin
		  P.fprintf stderr
		    "%a: state_check_with_before: not consumed variable: %a\n"
		    Loc.fprint loc0 fprint_dvar2 d2v
		end
	  else ()
	end in
    List.iter aux sbis
(* end of [state_check_with_before] *)

let state_update_with_before loc0
  (sty: statype2) (sbis: state_before): unit =
  let sub =
    SEnv3.sexp2_hypo_inst_and_add loc0 sty.statype2_svs sty.statype2_gua in
  let rec aux sbi =
    let d2v = sbi.sbi_dvar in match statype2_dvar2_assoc sty d2v with
      | Some s2e ->
	  let s2e_new = SEnv3.sexp2_open_and_add (sexp2_subst sub s2e) in
	    d2v.dvar2_type <- Some s2e_new
      | None -> d2v.dvar2_type <- sbi.sbi_type_opt in
    List.iter aux sbis
(* end of [state_update_with_before] *)

(* ****** ****** *)

let statype2_body_save (): statype2_body =
  let f d2v sty2_bd =
    if dvar2_is_linear d2v then
      (d2v, Some d2v.dvar2_master_type) :: sty2_bd
    else sty2_bd in
  let rec aux sty2_bd xs = match xs with
    | [] -> sty2_bd
    | x :: xs -> begin match x with
	| LDVSlam -> sty2_bd
	| LDVSllam _ -> aux sty2_bd xs
	| LDVSset d2vs ->
	    let sty2_bd = DvarSet.fold f d2vs sty2_bd in aux sty2_bd xs
      end in
  let sty2_bd = DvarSet.fold f !the_local_dvar2set [] in
    aux sty2_bd !the_local_dvar2set_list
(* end of [statype2_body_save] *)

let state_before_save (): state_before =
  let f d2v sbis =
    if dvar2_is_linear d2v then
      let sbi = {
	sbi_dvar= d2v;
	sbi_type_opt= d2v.dvar2_type;
	sbi_lin= d2v.dvar2_linear;
      } in sbi :: sbis
    else sbis in
  let rec aux sbis xs = match xs with
    | [] -> sbis
    | x :: xs -> begin match x with
	| LDVSlam -> sbis
	| LDVSllam _ -> aux sbis xs
	| LDVSset d2vs ->
	    let sbis = DvarSet.fold f d2vs sbis in aux sbis xs
      end in
  let sbis = DvarSet.fold f !the_local_dvar2set [] in
    aux sbis !the_local_dvar2set_list
(* end of [state_before_save] *)

let state_before_restore (sbis: state_before): unit =
  let f sbi =
    let d2v = sbi.sbi_dvar in begin
	d2v.dvar2_type <- sbi.sbi_type_opt;
	d2v.dvar2_linear <- sbi.sbi_lin
      end in
    List.iter f sbis
(* end of [state_before_restore] *)

(* ****** ****** *)

type state_afters_item = {
  sasi_dvar : dvar2;
  mutable sasi_types_opt : (sexp2 list) option;
  mutable sasi_lin : int;
} (* end of [state_afters_item] *)

type state_afters = {
  sas_item_list : state_afters_item list;
  mutable sas_stamps_ref_list : (stamps * SEnv3.cstr3 option ref) list;
} (* end of [state_afters] *)

(* ****** ****** *)

let state_afters_initialize (sbis: state_before): state_afters =
  let f sbi = 
    let d2v = sbi.sbi_dvar in
    let lin = d2v.dvar2_linear in {
	sasi_dvar= d2v;
	sasi_types_opt= Some [];
	sasi_lin= lin;
      } in
  let sasis = List.map f sbis in
    { sas_item_list= sasis; sas_stamps_ref_list= []; }
(* end of [state_afters_initialize] *)

let state_afters_merge loc0 (sas: state_afters) (sbis: state_before): unit =
  let aux sasi sbi =
    let d2v = sbi.sbi_dvar in
(*
    let () =
      P.fprintf stdout
	"state_afters_merge: aux: d2v = %a\n" fprint_dvar2 d2v in
    let () =
      P.fprintf stdout
	"state_afters_merge: aux: d2v.dvar2_linear = %i\n" d2v.dvar2_linear in
    let () =
      P.fprintf stdout
	"state_afters_merge: before: aux: sasi.sasi_lin = %i\n" sasi.sasi_lin in
*)
    let () = sasi.sasi_lin <- max sasi.sasi_lin d2v.dvar2_linear in
(*
    let () =
      P.fprintf stdout
	"state_afters_merge: after: aux: sasi.sasi_lin = %i\n" sasi.sasi_lin in
*)
      match sasi.sasi_types_opt, d2v.dvar2_type with
	| None, None -> ()
	| Some [], None -> (sasi.sasi_types_opt <- None)
	| Some s2es1, Some s2e ->
	    sasi.sasi_types_opt <- Some (s2e :: s2es1)
	| None, Some _ -> begin
	    P.fprintf stderr
	      "%a: state_afters_merge: not consumed variable: <%a>\n"
	      Loc.fprint loc0 fprint_dvar2 sbi.sbi_dvar;
	    Err.abort ();
	  end
	| Some _, None -> begin
	    P.fprintf stderr
	      "%a: state_afters_merge: not preserved variable: <%a>\n"
	      Loc.fprint loc0 fprint_dvar2 sbi.sbi_dvar;
	    Err.abort ();
	  end in
  let ss = SS.stamps_get () in
  let r: SEnv3.cstr3 option ref = ref None in
  let () = SEnv3.cstr_ref_add r in
    begin
      sas.sas_stamps_ref_list <- (ss, r) :: sas.sas_stamps_ref_list;
      List.iter2 aux sas.sas_item_list sbis
    end
(* end of [state_afters_merge] *)

(* ****** ****** *)

let state_check_with_before_and_afters_with_state loc0
  (sbis: state_before) (sas: state_afters) (sty: statype2): unit =
(*
  let () =
    P.fprintf stdout "state_check_...: sty = %a\n"
      fprint_statype2_body sty.statype2_body in
*)
  let aux_find sub sty d2v = match statype2_dvar2_assoc sty d2v with
    | Some s2e -> sexp2_subst sub s2e | None -> d2v.dvar2_master_type in
  let rec aux_item sub sbis sasis: unit = match sbis, sasis with
    | sbi :: sbis, sasi :: sasis -> begin
	let () =
	  if sasi.sasi_lin > sbi.sbi_lin then begin
	    let d2v = sbi.sbi_dvar in match sasi.sasi_types_opt with
	      | Some s2es -> begin match s2es with
		  | s2e :: s2es ->
		      let ()  = sasi.sasi_types_opt <- Some s2es in
		      let s2e_check = aux_find sub sty d2v in
			SOL.sexp2_tyleq_solve loc0 s2e s2e_check
		  | [] -> error_of_deadcode
		      "ats_trans3: state_check_with_before_and_afters_with_state"
		end
	      | None -> ()
	  end in
	  aux_item sub sbis sasis
      end
    | _, _ -> () in
  let rec aux_item_list sbis sasis ssrs = match ssrs with
    | (ss, r) :: ssrs ->
	let () = SEnv3.env_push () in
	let () = SS.stamps_set ss in
	let sub =
	  SEnv3.sexp2_inst_and_add loc0 sty.statype2_svs sty.statype2_gua in
	let () = aux_item sub sbis sasis in
	let s3is = SEnv3.env_pop () in
	let () = r := Some (SEnv3.cstr3_itms s3is) in
	  aux_item_list sbis sasis ssrs
    | [] -> () in
  let sasis = sas.sas_item_list in
  let ssrs = sas.sas_stamps_ref_list in
    aux_item_list sbis sasis ssrs
(* end of [state_check_with_before_and_afters_with_state] *)

let state_check_with_before_and_afters loc0
  (sbis: state_before) (sas: state_afters): unit =
  state_check_with_before_and_afters_with_state
    loc0 sbis sas statype2_nil
(* end of [state_check_with_before_and_afters] *)

(* ****** ****** *)

let state_update_with_before_and_afters_with_state loc0
  (sbis: state_before) (sas: state_afters) (sty: statype2): unit =
  let aux_find sub sty d2v =
    match statype2_dvar2_assoc sty d2v with
      | Some s2e -> sexp2_subst sub s2e | None -> d2v.dvar2_master_type in
  let rec aux sub sbis sasis = match sbis, sasis with
    | sbi :: sbis, sasi :: sasis -> begin
	let d2v = sbi.sbi_dvar in
	let () =
	  if sasi.sasi_lin > sbi.sbi_lin then begin
	    let () = d2v.dvar2_linear <- sasi.sasi_lin in
	      match sasi.sasi_types_opt with
		| Some _ -> d2v.dvar2_type <- Some (aux_find sub sty d2v)
		| None -> d2v.dvar2_type <- None
	  end in
	  aux sub sbis sasis
      end
    | _, _ -> () in
  let sub =
    SEnv3.sexp2_hypo_inst_and_add loc0 sty.statype2_svs sty.statype2_gua in
    aux sub sbis sas.sas_item_list
(* end of [state_update_with_before_and_afters_with_state] *)

let state_update_with_before_and_afters loc0
  (sbis: state_before) (sas: state_afters): unit =
  state_update_with_before_and_afters_with_state
    loc0 sbis sas statype2_nil
(* end of [state_update_with_before_and_afters] *)

(* ****** ****** *)

type lamloop =
  | LMLPlam
  | LMLPloop of
      state_before *
      statype2 (* init / continue *) *
      statype2 (* exit / break *) *
      (sexp2 list) option (* metric *)
  | LMLPnone
(* end of [lamloop] *)

let the_lamloop : lamloop ref = ref LMLPnone
let the_lamloop_list : (lamloop list) ref = ref []

let lamloop_pop (): unit =
  match !the_lamloop_list with
    | lmlp :: lmlps -> (the_lamloop := lmlp; the_lamloop_list := lmlps)
    | [] -> error "lamloop_pop"
(* end of [lamloop_pop] *)

let lamloop_push (lmlp: lamloop): unit = begin
  the_lamloop_list := !the_lamloop :: !the_lamloop_list;
  the_lamloop := lmlp
end (* end of [lamloop_push] *)

let lamloop_push_lam (): unit = lamloop_push (LMLPlam)

let lamloop_push_loop
  (sbis: state_before)
  (sty_init: statype2) (sty_exit: statype2)
  (met: sexp2 list option): unit = begin
  lamloop_push (LMLPloop (sbis, sty_init, sty_exit, met))
end (* end of [lamloop_push_loop] *)

let lamloop_exn (loc0: loc)
  : state_before * statype2 * statype2 * (sexp2 list) option =
  match !the_lamloop with
    | LMLPloop (sbis, sty_init, sty_exit, met) -> (sbis, sty_init, sty_exit, met)
    | LMLPlam -> begin
	P.fprintf stderr "%a: lamloop_exn: LMLPlam"
	  Loc.fprint loc0;
	prerr_newline ();
	Err.abort ()
      end
    | LMLPnone -> begin
	P.fprintf stderr "%a: lamloop_exn: LMLPnone"
	  Loc.fprint loc0;
	prerr_newline ();
	Err.abort ()
      end
(* end of [lamloop_exn] *)

(* ****** ****** *)

let initialize () = begin
  the_lamloop := LMLPnone;
  the_lamloop_list := [];

  the_local_dvar2set := DvarSet.empty;
  the_local_dvar2set_list := [];
end (* end of [initialize] *)

(* ****** ****** *)

(* end of [ats_dynenv3.ml] *)
