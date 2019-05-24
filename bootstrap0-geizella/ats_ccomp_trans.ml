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

open Ats_hiexp
open Ats_hiexp_util
open Ats_trans4

open Ats_ccomp
open Ats_ccomp_util

(* ****** ****** *)

module P = Printf

module Err = Ats_error
module Lab = Ats_label
module Loc = Ats_location
module Syn = Ats_syntax

(* ****** ****** *)

type loc = Loc.location
type stamp = Cnt.count

(* ****** ****** *)

(* two standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_ccomp_trans: "; Err.error s;
end

let error_with_loc (loc: loc) (s: string): 'a = begin
  prerr_string "ats_ccomp_trans: "; Err.error_with_loc loc s;
end

(* ****** ****** *)

let function_list_tailjoin loc_all
  (ctx: varctx) (fs0: function_t list): unit =
  let (f0, fs0) = match fs0 with
    | f :: fs -> (f, fs) | [] -> error_of_deadcode "functon_list_tailjoin" in
  let name_all =
    let aux_name f fs: string =
      let sb = Buffer.create 64 in (* 64: wild guess *)
      let () =
	let aux f =
	  let fl = f.function_lab in
	    (Buffer.add_char sb '_'; Buffer.add_string sb fl.funlab_name) in
	  (aux f; List.iter aux fs) in
	Buffer.contents sb in
      aux_name f0 fs0 in
  let hit0_res = (f0.function_ret).tmpvar_type in
  let tmp_ret_all = tmpvar_ret_new hit0_res in
  let () = (* checking return types *)
    let rec aux_ck f =
      let hit_res = (f.function_ret).tmpvar_type in
	if not (name_of_hityp hit0_res = name_of_hityp hit_res) then begin
	  P.eprintf
	    "%a: return type mismatch for mutual tail-recursion: %a <> %a\n"
	    Loc.fprint f.function_loc fprint_hityp hit0_res fprint_hityp hit_res;
	  Err.abort ();
	end in
      List.iter aux_ck fs0 in
  let fl_all =
    let fc = Syn.FUNCLOclo 1(*ref*) in
    let hits_arg = [hityp_int; hityp_vararg] in
    let hit_fun = hityp_fun fc hits_arg hit0_res in
      funlab_new_with_name_and_type name_all hit_fun in
  let vts_all = 
    let aux_vts f0 fs0: VarTypSet.t =
      List.fold_left
	(fun vts f -> VarTypSet.union vts (f.function_vts))
	f0.function_vts fs0 in
      aux_vts f0 fs0 in
  let env_all =
    let aux_env f0 fs0: VarTypSet.t =
      List.fold_left
	(fun vts f -> VarTypSet.union vts (function_environment f))
	(function_environment f0) fs0 in
      aux_env f0 fs0 in
  let (tag_fl_tmps_lst, res_all) = (* update *)
    let vp_fun = valprim_clo 0 fl_all ctx in
    let rec aux_update tag_fl_tmps_lst ifun_lst tag = function
      | f :: fs ->
	  let fl = f.function_lab in
	  let hits_arg = funlab_type_arg fl in
	  let tmps_arg = fl.funlab_tailjoined in
	  let tag_fl_tmps_lst = (tag, fl, tmps_arg) :: tag_fl_tmps_lst in
	  let ifun_lst =
	    let vps = List.map valprim_tmp tmps_arg in
	    let ifun =
	      Ifunction (tmp_ret_all, vps, f.function_body, f.function_ret) in
	      ifun :: ifun_lst in
	  let vp_tag = valprim_int tag in
	  let vps_arg =
	    let rec aux i = function
	      | hit :: hits -> (* need for special handling of refarg *)
		  let hit_arg = match hit.hityp_node with
		    | HITrefarg _ -> hityp_ptr | _ -> hit in
		  let vp_arg =
		    { valprim_node= VParg i; valprim_type= hit_arg; } in
		    vp_arg :: aux (i+1) hits
	      | [] -> [] in
	      aux 0 hits_arg in
	  let tmp_ret =
	    let hit_res = (f.function_ret).tmpvar_type in
	      tmpvar_ret_new hit_res in
	  let i = Icall
            (tmp_ret, fl_all.funlab_type, vp_fun, vp_tag :: vps_arg) in
	  let _ (* function_t *) =
	    function_store_add f.function_loc fl
	      f.function_level VarTypSet.empty [fl_all] tmp_ret [i] in
	    aux_update tag_fl_tmps_lst ifun_lst (tag+1) fs
      | [] -> (List.rev tag_fl_tmps_lst, List.rev ifun_lst) in
      aux_update [] [] 0 (f0 :: fs0) in
  let f_all =
    function_store_add loc_all fl_all f0.function_level
      vts_all [] (* function_fl_lst *) tmp_ret_all res_all in
    begin
      f_all.function_env <- Some env_all;
      f_all.function_tailjoin <- tag_fl_tmps_lst;
    end

(* ****** ****** *)

let the_freed_valprim_list: valprim list ref = ref []
let freed_valprim_list_add (vp: valprim): unit =
  the_freed_valprim_list := vp :: !the_freed_valprim_list
let freed_valprim_list_get (): valprim list =
  List.rev (!the_freed_valprim_list)
let freed_valprim_list_reset (): unit =
  the_freed_valprim_list := []

let rec ccomp_match
  (level: int)
  (k_fail_opt: cont_t option)
  (ctx: varctx)
  (res: instr_t list)
  (vp: valprim)
  (hip0: hipat)
  : varctx * instr_t list =
  match hip0.hipat_node with
    | HIPany -> (ctx, res)
    | HIPbool b ->
	let res = match k_fail_opt with
	  | Some k_fail -> ipatck res vp (PATCKbool b) k_fail
	  | None -> res in (ctx, res)
    | HIPchar c ->
	let res = match k_fail_opt with
	  | Some k_fail -> ipatck res vp (PATCKchar c) k_fail
	  | None -> res in (ctx, res)
    | HIPcon (freeknd, hit_sum, d2c, hips_arg) -> begin
        let () = dyncon_set_add d2c in
(*
	let () = 
	  P.fprintf stdout "ccomp_match: HIPcon: before: hit_sum = %a\n"
	    fprint_hityp hit_sum in
*)
	let hit_sum =
	  if hipat_list_is_used hips_arg then hityp_nf hit_sum else hit_sum in
(*
	let () = 
	  P.fprintf stdout "ccomp_match: HIPcon: after: hit_sum = %a\n"
	    fprint_hityp hit_sum in
*)
	  ccomp_match_con level k_fail_opt ctx res vp freeknd hit_sum d2c hips_arg
      end
    | HIPempty -> (ctx, res)
    | HIPint i ->
	let res = match k_fail_opt with
	  | Some k_fail -> ipatck res vp (PATCKint i) k_fail
	  | None -> res in (ctx, res)
    | HIPrec (is_flat, hit_rec, lhips) -> begin
	let hit_rec = hityp_nf hit_rec in
	  ccomp_match_rec level k_fail_opt ctx res vp is_flat hit_rec lhips
      end
    | HIPstring s ->
	let res = match k_fail_opt with
	  | Some k_fail -> ipatck res vp (PATCKstring s) k_fail
	  | None -> res in (ctx, res)
    | HIPvar (_(*isref*), d2v, ohip) -> begin
	if dvar2_is_used d2v then begin
	  let () = d2v.dvar2_level <- level in
	  let ismove = begin
	    if dvar2_is_mutable d2v then false else valprim_is_mutable vp
	  end in
	    if ismove then begin
	      let tmp = tmpvar_new vp.valprim_type in
	      let res = imove_val res tmp vp in
	      let vp_new = valprim_tmp tmp in
	      let ctx = varctx_add ctx d2v vp_new in
		ccomp_match_opt level k_fail_opt ctx res vp_new ohip
	    end else begin
	      let ctx = varctx_add ctx d2v vp in
		ccomp_match_opt level k_fail_opt ctx res vp ohip
	    end
	end else begin
	  ccomp_match_opt level k_fail_opt ctx res vp ohip
	end
      end (* end of [HIPvar] *)
    | _ -> begin
	error_of_unavailability "ats_ccomp: ccomp_match"
      end

and ccomp_match_list
  (level: int) (k_fail_opt: cont_t option) (ctx: varctx)
  (res: instr_t list) (vps: valprim list) (hips: hipat list)
  : varctx * instr_t list =
  let rec aux ctx res vps hips = match vps, hips with
    | [], [] -> (ctx, res)
    | vp :: vps, hip :: hips ->
	let (ctx, res) = ccomp_match level k_fail_opt ctx res vp hip in
	  aux ctx res vps hips 
    | _, _ -> error_of_deadcode "ats_ccomp_trans: ccomp_match_list" in
    aux ctx res vps hips

and ccomp_match_opt
  (level: int) (k_fail_opt: cont_t option) (ctx: varctx)
  (res: instr_t list) (vp: valprim) (ohip: hipat option)
  : varctx * instr_t list = begin
  match ohip with
    | Some hip -> ccomp_match level k_fail_opt ctx res vp hip
    | None -> (ctx, res)
 end (* end of [ccomp_match_opt] *)

and ccomp_match_con
  (level: int)
  (k_fail_opt: cont_t option)
  (ctx: varctx)
  (res: instr_t list)
  (vp: valprim)
  (freeknd: int)
  (hit_sum: hityp)
  (d2c: dcon2)
  (hips_arg: hipat list)
  : varctx * instr_t list =
  let hits_arg =
    List.map (function hip -> hip.hipat_type) hips_arg in
  let res = match k_fail_opt with
    | Some k_fail -> begin
	let patck =  
	  if dcon2_is_exn d2c then PATCKexn d2c else PATCKcon d2c in
	  ipatck res vp patck k_fail
      end
    | None -> res in
  let rec aux i ctx res hips_arg hits_arg =
    match hips_arg, hits_arg with
      | hip_arg :: hips_arg, hit_arg :: hits_arg -> begin 
	  match hip_arg.hipat_node with
            | HIPany -> aux (i+1) ctx res hips_arg hits_arg
	    | HIPvar (_, d2v, None) when dvar2_is_unused d2v ->
		aux (i+1) ctx res hips_arg hits_arg
            | HIPvar (true, d2v, ohip) -> begin
		let tmp_ptr = tmpvar_new hityp_ptr in
		let res = iselcon_ptr res tmp_ptr vp hit_sum i in
		let vp_ptr = valprim_tmp tmp_ptr in
		let ctx = varctx_add ctx d2v vp_ptr in match ohip with
		  | Some hip ->
                      let tmp_arg = tmpvar_new hit_arg in
                      let res = iload_ptr_offs res tmp_arg vp_ptr [] in
                      let vp_arg = valprim_tmp tmp_arg in
                      let (ctx, res) = 
                        ccomp_match level k_fail_opt ctx res vp_arg hip in
                        aux (i+1) ctx res hips_arg hits_arg
		  | None -> aux (i+1) ctx res hips_arg hits_arg
	      end
	    | _ -> begin
		let tmp = tmpvar_new hit_arg in
		let res = iselcon res tmp vp hit_sum i in
		let vp_arg = valprim_tmp tmp in
		let (ctx, res) =
		  ccomp_match level k_fail_opt ctx res vp_arg hip_arg in
		  aux (i+1) ctx res hips_arg hits_arg
	      end
	end
      | [], [] -> begin
	  let () =
	    if i <> 0 then (* a constructor carrying arguments *)
	      if freeknd < 0 then (* constructor needs to be freed *)
		freed_valprim_list_add vp
	      else ()
	    else () in
	    (ctx, res)
	end
      | _, _ -> error_of_deadcode "ccomp_match_con: aux" in
    aux 0 ctx res hips_arg hits_arg  

and ccomp_match_rec
  (level: int)
  (k_fail_opt: cont_t option)
  (ctx: varctx)
  (res: instr_t list)
  (vp: valprim)
  (is_flat: bool)
  (hit_rec: hityp)
  (lhips: labhipat list)
  : varctx * instr_t list =
(*
  let () =
    P.fprintf stdout "ccomp_match_rec: vp = %a\n" fprint_valprim vp in
  let () =
    P.fprintf stdout "ccomp_match_rec: vp.valprim_type = %a\n"
      fprint_sexp2 vp.valprim_type in
  let () =
    P.fprintf stdout "ccomp_match_rec: lhips = %a\n" fprint_labhipat_list lhips in
*)
  let rec aux ctx res lhips = match lhips with
    | (l, hip) :: lhips ->
	let tmp = tmpvar_new hip.hipat_type in
	let res = iselect res tmp vp [OFFlab (l, hit_rec)] in
	let vp_tmp = valprim_tmp tmp in
	let (ctx, res) = ccomp_match level k_fail_opt ctx res vp_tmp hip in
	  aux ctx res lhips
    | [] -> (ctx, res) in
    aux ctx res lhips

(* ****** ****** *)

let ccomp_funarg
  (fl: funlab) (k_fail_opt: cont_t option) (ctx: varctx)
  (prolog: instr_t list) (hips: hipat list): varctx * instr_t list =
  let level = dvar2_level_get () in
  let rec aux ctx res n hips = match hips with
    | hip :: hips ->
	let hit = hip.hipat_type in
	let vp_arg = valprim_arg n hit in
	let (ctx, res) = ccomp_match level k_fail_opt ctx res vp_arg hip in
	  aux ctx res (n+1) hips
    | [] -> (ctx, res) in
    aux ctx prolog 0 hips

(* ****** ****** *)

let rec ccomp_exp (ctx: varctx)
  (res: instr_t list) (hie0: hiexp): instr_t list * valprim =
  let hit0 = hie0.hiexp_type in match hie0.hiexp_node with
    | HIEassgn_ptr (hie_ptr, hils, hie_val) ->
	let res = ccomp_exp_assgn_ptr ctx res hie_ptr hils hie_val in
	  (res, valprim_void ())
    | HIEassgn_var (d2v_ptr, hils, hie_val) ->
	let res = ccomp_exp_assgn_var ctx res d2v_ptr hils hie_val in
	  (res, valprim_void ())
    | HIEbool b -> let vp = valprim_bool b in (res, vp)
    | HIEcastfn (d2c, hie_arg) -> begin
        let (res, vp_arg) = ccomp_exp ctx res hie_arg in
          (res, valprim_castfn d2c vp_arg hit0)
      end (* end of [HIEcastfn] *)
    | HIEchar c -> let vp = valprim_char c in (res, vp)
    | HIEcst d2c -> begin
	let () = dyncst_set_add d2c in
	let vp = match toplevel_cstctx_find d2c with
	  | Some vp -> vp | None -> valprim_cst d2c hit0 in
	  (res, vp)
      end
    | HIEdynload f -> begin
	let vp = valprim_void () in (Iload_file f :: res, vp)
      end
    | HIEempty -> let vp = valprim_void () in (res, vp)
    | HIEextval code -> let vp = valprim_ext code hit0 in (res, vp)
    | HIEfloat f -> let vp = valprim_float f in (res, vp)
    | HIEfreeat hie ->
	let res = ccomp_exp_freeat ctx res hie in (res, valprim_void ())
    | HIEint (ik, i) -> let vp = valprim_intinf ik i in (res, vp)
    | HIElam (hips_arg, hie_body) -> begin
	let fl = funlab_new_with_type hit0 in
	let () = tailjoin_list_push_mrk () in
	let () = tailjoin_list_push_lab fl [] in
	let prolog = [Ilabel_fun fl] in
	let _ (* function_t *) =
	  ccomp_exp_lam_with_funlab fl ctx prolog hips_arg hie_body in
	let () = tailjoin_list_pop () in
	let fcr = match hityp_funclo_get hit0 with
	  | Some fcr -> fcr
	  | None -> begin
	      error_of_deadcode "ats_ccomp_trans: ccomp_exp: HIElam: fcr"
	    end in
	let vp_lam = match fcr with
	  | Syn.FUNCLOclo i -> valprim_clo i fl ctx
	  | Syn.FUNCLOfun -> valprim_fun fl in
	  (res, vp_lam)
      end
    | HIEloopexn i ->
	let lab = loopexnlabs_list_get i in
	let vp = valprim_void () in (iloopexn res i lab, vp)
    | HIEptrof_ptr (hie_ptr, hils) ->
	ccomp_exp_ptrof_ptr ctx res hie_ptr hils
    | HIEptrof_var (d2v_ptr, hils) ->
	ccomp_exp_ptrof_var ctx res d2v_ptr hils
    | HIErefarg (refval, freeknd, hie) -> ccomp_exp_refarg ctx res refval hie
    | HIEsizeof hit ->
	let vp = valprim_sizeof (hityp_nf hit) in (res, vp)
    | HIEstring s -> let vp = valprim_string s in (res, vp)
    | HIEtemplate_cst (d2c, hitss) ->
	ccomp_exp_template_cst hie0.hiexp_loc res hit0 d2c hitss
    | HIEtemplate_var (d2v, hitss) ->
	ccomp_exp_template_var hie0.hiexp_loc res hit0 d2v hitss
    | HIEtop -> let vp = valprim_top hit0 in (res, vp)
    | HIEvar d2v -> let vp = ccomp_exp_var ctx d2v in (res, vp)
    | HIEwhile (hie_test, hie_body) ->
	let res = ccomp_exp_while ctx res hie_test hie_body in
	  (res, valprim_void ())
    | _ -> begin
(*
	let () =
	  P.fprintf stdout "ccomp_exp: hie0 = %a\n" fprint_hiexp hie0 in
	let () = 
	  P.fprintf stdout "ccomp_exp: hit0 = %a\n" fprint_hityp hit0 in
*)
	let tmp_res = tmpvar_new hit0 in
(*
	let () = 
	  P.fprintf stdout "ccomp_exp: tmp_res = %a\n" fprint_tmpvar tmp_res in
*)
	let res = ccomp_exp_with_tmpvar ctx res tmp_res hie0 in
	let vp = valprim_tmp tmp_res in (res, vp)
      end

and ccomp_exp_list (ctx: varctx)
  (res: instr_t list) (hies: hiexp list): instr_t list * valprim list =
  let rec aux res vps = function
    | hie :: hies ->
	let (res, vp) = ccomp_exp ctx res hie in
	  aux res (vp :: vps) hies
    | [] -> (res, List.rev vps) in
    aux res [] hies

and ccomp_labexp_list (ctx: varctx)
  (res: instr_t list) (lhies: labhiexp list): instr_t list * labvalprim list =
  let rec aux res lvps = function
    | (l, hie) :: lhies ->
	let (res, vp) = ccomp_exp ctx res hie in
	  aux res ((l, vp) :: lvps) lhies
    | [] -> (res, List.rev lvps) in
    aux res [] lhies

and ccomp_exp_list_list (ctx: varctx) (res: instr_t list)
  (hiess: hiexp list list): instr_t list * valprim list list =
  let rec aux res vpss = function
    | hies :: hiess ->
	let (res, vps) = ccomp_exp_list ctx res hies in
	  aux res (vps :: vpss) hiess
    | [] -> (res, List.rev vpss) in
    aux res [] hiess

(* ****** ****** *)

and ccomp_exp_template_cst loc (res: instr_t list)
  (hit0: hityp) (d2c0: dcst2) (hitss: hityp list list): instr_t list * valprim =
  let (decarg_def, hie_def) =
    match tempdef_cst_tbl_find d2c0 with
      | Some (decarg, hie) -> (decarg, hie)
      | None -> begin
	  P.eprintf "%a: no template definition for <%a>\n"
	    Loc.fprint loc fprint_dcst2 d2c0;
	  Err.abort ()
	end in
  let ctx_def = varctx_nil in
  let basename = d2c0.dcst2_fullname_id in
  let fullname = template_name basename hitss in
(*
  let () =
    P.fprintf stdout "ccomp_exp_template_cst: hit0 = %a\n" fprint_hityp hit0 in
  let () =
    P.fprintf stdout "ccomp_exp_template_cst: fullname = %s\n" fullname in
*)
  let ovp = tmpinst_cst_tbl_find fullname in match ovp with
    | None -> begin
	let fl = funlab_new_with_name_and_type fullname hit0 in
	let sub = template_bind decarg_def hitss in
(*
	let () =
	  let f (s2v, hit) =
	    P.fprintf stdout "  s2v = %a and hit = %a\n"
	      fprint_svar2 s2v fprint_hityp hit in
	  let () = P.fprintf stdout "ccomp_exp_template_cst:\n" in
	    List.iter f sub in
*)
	let () = svar2_hityp_list_push sub in
	let fcr = match hityp_funclo_get hit0 with
	  | Some fcr -> fcr
	  | None -> begin
	      error_of_deadcode "ats_ccomp_trans: ccomp_exp_template_cst: fcr"
	    end in
	let vp_lam = match fcr with
	  | Syn.FUNCLOclo i -> valprim_clo i fl ctx_def
	  | Syn.FUNCLOfun -> valprim_fun fl in
	let () = tmpinst_cst_tbl_add fullname vp_lam in
	let () = tailjoin_list_push_mrk () in
	let () = tailjoin_list_push_lab fl [] in
	let prolog = [Ilabel_fun fl] in
	let _ (* function_t *) = match hie_def.hiexp_node with
	  | HIElam (hips_arg, hie_body) ->
	      ccomp_exp_lam_with_funlab fl ctx_def prolog hips_arg hie_body
	  | _ -> error_of_deadcode
	      "ats_ccomp_trans: ccomp_exp_template_cst: not function" in
	let () = tailjoin_list_pop () in
	let () = svar2_hityp_list_pop () in
	  (res, vp_lam)
      end
    | Some vp_lam -> (res, vp_lam)

(* ****** ****** *)

and ccomp_exp_template_var loc (res: instr_t list)
  (hit0: hityp) (d2v0: dvar2) (hitss: hityp list list): instr_t list * valprim =
  let hie_def = match tempdef_var_map_find d2v0 with
    | Some hie -> hie
    | None ->  begin
	P.eprintf "%a: no template definition for <%a>\n"
	  Loc.fprint loc fprint_dvar2 d2v0;
	Err.abort ()
      end in
  let ctx_def = varctx_nil in
  let basename = Syn.string_of_did d2v0.dvar2_name in
  let fullname = template_name basename hitss in
(*
  let () =
    P.fprintf stdout "ccomp_exp_template_var: hit0 = %a\n" fprint_hityp hit0 in
  let () =
    P.fprintf stdout "ccomp_exp_template_var: fullname = %s\n" fullname in
*)
  let ovp = tmpinst_var_tbl_find fullname in match ovp with
    | None -> begin
	let fl = funlab_new_with_name_and_type fullname hit0 in
	let sub = template_bind d2v0.dvar2_decarg hitss in
(*
	let () =
	  let f (s2v, hit) =
	    P.fprintf stdout "  s2v = %a and hit = %a\n"
	      fprint_svar2 s2v fprint_hityp hit in
	  let () = P.fprintf stdout "ccomp_exp_template_var:\n" in
	    List.iter f sub in
*)
	let () = svar2_hityp_list_push sub in
	let fcr = match hityp_funclo_get hit0 with
	  | Some fcr -> fcr
	  | None -> begin
	      error_of_deadcode "ats_ccomp_trans: ccomp_exp_template_var: fcr"
	    end in
	let vp_lam = match fcr with
	  | Syn.FUNCLOclo i -> valprim_clo i fl ctx_def
	  | Syn.FUNCLOfun -> valprim_fun fl in
	let () = tmpinst_var_tbl_add fullname vp_lam in
	let () = tailjoin_list_push_mrk () in
	let () = tailjoin_list_push_lab fl [] in
	let prolog = [Ilabel_fun fl] in
	let _ (* function_t *) = match hie_def.hiexp_node with
	  | HIElam (hips_arg, hie_body) ->
	      ccomp_exp_lam_with_funlab fl ctx_def prolog hips_arg hie_body
	  | _ -> error_of_deadcode
	      "ats_ccomp_trans: ccomp_exp_template_var: not function" in
	let () = tailjoin_list_pop () in
	let () = svar2_hityp_list_pop () in
	  (res, vp_lam)
      end
    | Some vp_lam -> (res, vp_lam)

(* ****** ****** *)

and ccomp_exp_thunk (ctx: varctx) (hie: hiexp): valprim =
  let hit = hie.hiexp_type in
  let hit_clo = hityp_fun (Syn.FUNCLOclo 0(*ptr*)) [] hit in
  let fl = funlab_new_with_type hit_clo in
  let () = tailjoin_list_push_mrk () in
  let () = tailjoin_list_push_lab fl [] in
  let prolog = [Ilabel_fun fl] in
  let _ (* function_t *) =
    ccomp_exp_lam_with_funlab fl ctx prolog [] hie in
  let () = tailjoin_list_pop () in
    valprim_clo 0 fl ctx

(* ****** ****** *)

and ccomp_exp_with_tmpvar (ctx: varctx)
  (res: instr_t list) (tmp_res: tmpvar) (hie0: hiexp): instr_t list =
  let hit0 = hie0.hiexp_type in match hie0.hiexp_node with
    | HIEapp (hit_fun, hie_fun, hies_arg) -> begin
	let (ctx, res, hie_fun, hies_arg, vps_free) =
	  let (ctx, res, hie_fun, ovp) = hiexp_app_proc ctx res hie_fun in
	  let (ctx, res, hies_arg, vps) = hiexp_app_list_proc ctx res hies_arg in
	  let vps = match ovp with Some vp -> vp :: vps | None -> vps in
	    (ctx, res, hie_fun, hies_arg, vps) in
	let hit_fun = hityp_nf hit_fun in
	let (res, vp_fun) = ccomp_exp ctx res hie_fun in
	let is_tail = match vps_free with
	  | [] when tmp_res.tmpvar_isret ->
	      begin match vp_fun.valprim_node with
		| VPfun fl -> tailjoin_list_find fl
		| VPclo (_, fl, _) -> tailjoin_list_find fl
		| _ -> None
	      end
	  | _ -> None in
	let res = match is_tail with
	  | Some (fl, tmps_arg) -> begin
	      let (res, vps_arg) =
		let rec aux res vps = function
		  | hie :: hies ->
		      let hit = hie.hiexp_type in
		      let tmp = tmpvar_new hit in
		      let res = ccomp_exp_with_tmpvar ctx res tmp hie in
		      let vp = valprim_tmp tmp in aux res (vp :: vps) hies
		  | [] -> (res, List.rev vps) in
		  aux res [] hies_arg in
		icall_tail res tmp_res fl tmps_arg vps_arg
	    end
	  | None -> begin
	      let (res, vps_arg) = ccomp_exp_list ctx res hies_arg in
		icall res tmp_res hit_fun vp_fun vps_arg
	    end in
	  List.fold_left ifreeptr res vps_free
      end
    | HIEarr (hit_elt, hies_elt) -> begin
	let hit_elt = hityp_nf hit_elt in
	  ccomp_exp_arr_with_tmpvar ctx res tmp_res hit_elt hies_elt
      end
    | HIEassgn_ptr (hie_ptr, hils, hie_val) ->
	ccomp_exp_assgn_ptr ctx res hie_ptr hils hie_val
    | HIEassgn_var (d2v_ptr, hils, hie_val) ->
	ccomp_exp_assgn_var ctx res d2v_ptr hils hie_val
    | HIEbool b -> imove_val_bool res tmp_res b
    | HIEcase (is_exhaustive, hies, hicls) ->
	let (res, vps) = ccomp_exp_list ctx res hies in
	let k_fail_opt =
	  if is_exhaustive then None else Some (CONTmatch_fail) in
	let brs = ccomp_hicla_list k_fail_opt ctx tmp_res vps hicls in
	  iswitch res brs
    | HIEcastfn (d2c, hie_arg) ->
         ccomp_exp_with_tmpvar ctx res tmp_res hie_arg
      (* end of [HIEcastfn] *)
    | HIEchar c ->
         imove_val_char res tmp_res c
      (* end of [HIEchar] *)
    | HIEcon (hit_sum, d2c, hies_arg) ->
(*
	let () =
	  P.fprintf stdout "ccomp_exp_with_tmpvar: HIEcon: d2c = %a\n"
	    fprint_dcon2 d2c in
	let () =
	  P.fprintf stdout "ccomp_exp_with_tmpvar: HIEcon: hies_arg = %a\n"
	    fprint_hiexp_list hies_arg in
*)
        let () = dyncon_set_add d2c in 
	let hit_sum = hityp_nf hit_sum in
	let (res, vps) = ccomp_exp_list ctx res hies_arg in
	  imove_con res tmp_res hit_sum d2c vps
    | HIEcst d2c ->
	let () = dyncst_set_add d2c in
	let vp = match toplevel_cstctx_find d2c with
	  | Some vp -> vp | None -> valprim_cst d2c hit0 in
	  imove_val res tmp_res vp
    | HIEdelay (lin, hie) -> begin
	let vp_clo = ccomp_exp_thunk ctx hie in
	let d2c =
	  if lin > 0 then dcon2_thunkvalue_vt_thunk ()
	  else dcon2_thunkvalue_thunk () in
        let () = dyncon_set_add d2c in 
	let hit = hie.hiexp_type in
	let hit_sum = hityp_sum_tmp d2c [hit] in
	let tmp_con_res = tmpvar_new hityp_ptr in
	let hit_sum = hityp_nf hit_sum in
(*
	let () =
	  P.fprintf stdout "ccomp_exp_with_tmpvar: HIEdelay: hit_sum = %a\n"
	    fprint_hityp hit_sum in
*)
	let res = imove_con res tmp_con_res hit_sum d2c [vp_clo] in
	let vp_con = valprim_tmp tmp_con_res in
	  if lin > 0 then imove_val res tmp_res vp_con else irefval res tmp_res vp_con
      end
    | HIEdynload f -> Iload_file f :: res
    | HIEempty -> res
    | HIEextval code -> imove_val_ext res tmp_res code hit0
    | HIEfloat f -> imove_val_float res tmp_res f
    | HIEfix (d2v_fix, hie_def) -> begin
	let ctx = varctx_add ctx d2v_fix (valprim_tmp tmp_res) in
	  ccomp_exp_with_tmpvar ctx res tmp_res hie_def
      end
    | HIEfreeat hie -> ccomp_exp_freeat ctx res hie
    | HIEif (hie_cond, hie_then, hie_else) -> begin
	let (res, v_cond) = ccomp_exp ctx res hie_cond in
	let tmp1_res = tmpvar_new_with_root tmp_res in
	let res1 = ccomp_exp_with_tmpvar ctx [] tmp1_res hie_then in
	let tmp2_res = tmpvar_new_with_root tmp_res in
	let res2 = ccomp_exp_with_tmpvar ctx [] tmp2_res hie_else in
	  Icond (v_cond, List.rev res1, List.rev res2) :: res
      end
    | HIEint (ik, i) -> imove_val_int res tmp_res ik i
    | HIElam (hips_arg, hie_body) -> begin
	let fl = funlab_new_with_type hit0 in
	let () = tailjoin_list_push_mrk () in
	let () = tailjoin_list_push_lab fl [] in
	let prolog = [Ilabel_fun fl] in
	let _ (* function_t *) =
	  ccomp_exp_lam_with_funlab fl ctx prolog hips_arg hie_body in
	let () = tailjoin_list_pop () in
	let fcr = match hityp_funclo_get hit0 with
	  | Some fcr -> fcr
	  | None -> begin
	      error_of_deadcode "ats_ccomp_trans: ccomp_exp_with_tempvar: fcr"
	    end in
	let vp_lam = match fcr with
	  | Syn.FUNCLOclo i -> valprim_clo i fl ctx
	  | Syn.FUNCLOfun -> valprim_fun fl in
	  imove_val res tmp_res vp_lam
      end
    | HIElet (hids, hie_body) ->
	let (ctx, res) = ccomp_dec_list ctx res hids in
	  ccomp_exp_with_tmpvar ctx res tmp_res hie_body
    | HIEloopexn i ->
	let lab = loopexnlabs_list_get i in iloopexn res i lab
    | HIElst hies_elt ->
	ccomp_exp_lst_with_tmpvar ctx res tmp_res hies_elt
    | HIEptrof_ptr (hie_ptr, hils) ->
	let (res, vp) = ccomp_exp_ptrof_ptr ctx res hie_ptr hils in
	  imove_val res tmp_res vp
    | HIEptrof_var (d2v_ptr, hils) ->
	let (res, vp) = ccomp_exp_ptrof_var ctx res d2v_ptr hils in
	  imove_val res tmp_res vp
    | HIEraise hie_exn ->
	let (res, vp) = ccomp_exp ctx res hie_exn in iraise res vp
    | HIErec (is_flat, hit_rec, lhies) ->
	let hit_rec = hityp_nf hit_rec in begin match lhies with
	| [l, hie] when hityp_is_singular_rec hit0 ->
	    let (res, vp) = ccomp_exp ctx res hie in
	      imove_val res tmp_res vp
	| _ -> begin
	    let (res, lvps) = ccomp_labexp_list ctx res lhies in
	      imove_rec is_flat res tmp_res hit_rec lvps
	  end
      end
    | HIErefarg (refval, freeknd, hie) ->
	let (res, vp_ptr) = ccomp_exp_refarg ctx res refval hie in
	  imove_val res tmp_res vp_ptr
    | HIEseq hies -> ccomp_exp_seq_with_tmpvar ctx res tmp_res hies
    | HIEsel (hie_root, hils) ->
	let (res, vp_root) = ccomp_exp ctx res hie_root in
	let (res, offs) = ccomp_hilab_list ctx res hils in
	  iselect res tmp_res vp_root offs
    | HIEsel_ptr (hie_ptr, hils) ->
	let (res, vp_ptr) = ccomp_exp ctx res hie_ptr in
	let (res, offs) = ccomp_hilab_list ctx res hils in
	  iload_ptr_offs res tmp_res vp_ptr offs
    | HIEsel_var (d2v, hils) ->
	let vp_var = ccomp_exp_var ctx d2v in
	let (res, offs) = ccomp_hilab_list ctx res hils in
	  iload_var_offs res tmp_res vp_var offs
    | HIEsizeof hit -> imove_val_sizeof res tmp_res hit
    | HIEstring s -> imove_val_string res tmp_res s
    | HIEtop -> res (* nothing needs to be done *)
    | HIEtrywith (hie, hicls) ->
	let res_try =
	  List.rev (ccomp_exp_with_tmpvar ctx [] tmp_res hie) in
	let hit_exn = hityp_ptr in
	let tmp_exn = tmpvar_new hit_exn in
	let vp_exn = valprim_tmp tmp_exn in
	let k_fail_opt = Some (CONTraise vp_exn) in
	let brs = ccomp_hicla_list k_fail_opt ctx tmp_res [vp_exn] hicls in
	  Itrywith (res_try, tmp_exn, brs) :: res
    | HIEvar d2v ->
	let vp = ccomp_exp_var ctx d2v in imove_val res tmp_res vp
    | HIEwhile (hie_test, hie_body) ->
	ccomp_exp_while ctx res hie_test hie_body
    | _ -> begin
	P.fprintf stderr "%a: ccomp_exp_with_tmpvar: hie0 = %a\n"
	  Loc.fprint hie0.hiexp_loc fprint_hiexp hie0;
	Err.abort ();
      end
	
(* ****** ****** *)
	
(*
viewtypedef
arrayptrsize_viewtype_int_viewtype
  (a: viewtype, n:int) = [l:addr | l <> null] (@[a][n] @ l | ptr l, int n)
*)
	
and ccomp_exp_arr_with_tmpvar (ctx: varctx) (res: instr_t list)
  (tmp_res: tmpvar) (hit_elt: hityp) (hies_elt: hiexp list): instr_t list =
  let sz = List.length hies_elt in
  let res = iarray res tmp_res sz hit_elt in
  let tmp_arr = tmpvar_new hityp_ptr in
  let vp_arr = valprim_tmp tmp_arr in
  let res =
    let vp_res = valprim_tmp tmp_res in
    let off_lab = (* atslab_2 *)
      OFFlab (Lab.make_with_int 2, tmp_res.tmpvar_type) in
      iload_var_offs res tmp_arr vp_res [off_lab] in
  let rec aux_elts res i = function
    | hie_elt :: hies_elt ->
	let (res, vp_elt) = ccomp_exp ctx res hie_elt in
	let off_ind = OFFind ([[valprim_int i]], hit_elt) in
	let res = istore_ptr_offs res vp_arr [off_ind] vp_elt in
	  aux_elts res (i+1) hies_elt
    | [] -> res in
    aux_elts res 0 hies_elt
      
and ccomp_exp_lst_with_tmpvar (ctx: varctx)
  (res: instr_t list) (tmp_res: tmpvar) (hies_elt: hiexp list): instr_t list =
  match hies_elt with
  | _ :: _ -> begin
      ccomp_exp_lst1_with_tmpvar ctx res tmp_res hies_elt
    end
  | [] -> begin
      let d2c_nil = dcon2_list_nil () in
      let hit_nil = hityp_sum_make d2c_nil [] in
	imove_con res tmp_res hit_nil d2c_nil []
    end

and ccomp_exp_lst1_with_tmpvar (ctx: varctx)
  (res: instr_t list) (tmp_res: tmpvar) (hies_elt: hiexp list): instr_t list =
  let d2c_nil = dcon2_list_nil () in
  let hit_nil = hityp_sum_make d2c_nil [] in
  let d2c_cons = dcon2_list_cons () in
  let res = imove_con res tmp_res hit_nil d2c_nil [] in
  let rec aux_elts vp_res tmp_lst vp_lst res = function
    | vp_elt :: vps_elt ->
	let hit_cons =
	  let hit_elt = hityp_nf vp_elt.valprim_type in
	  let hit_res = hityp_nf vp_res.valprim_type in
	    hityp_sum_make d2c_cons [hit_elt; hit_res] in
	let res = imove_con res tmp_lst hit_cons d2c_cons [vp_elt; vp_res] in
	let res = imove_val res tmp_res vp_lst in
	  aux_elts vp_res tmp_lst vp_lst res vps_elt
    | [] -> res in
  let (res, vps_elt) = ccomp_exp_list ctx res hies_elt in
  let vp_res = valprim_tmp tmp_res in
  let tmp_lst = tmpvar_new tmp_res.tmpvar_type in
  let vp_lst = valprim_tmp tmp_lst in
    aux_elts vp_res tmp_lst vp_lst res (List.rev vps_elt)
	  
(* ****** ****** *)
	  
and ccomp_exp_assgn_ptr (ctx: varctx) (res: instr_t list)
  (hie_ptr: hiexp) (hils: hilab list) (hie_val: hiexp): instr_t list =
  let (res, vp_ptr) = ccomp_exp ctx res hie_ptr in
  let (res, offs) = ccomp_hilab_list ctx res hils in
  let (res, vp_val) = ccomp_exp ctx res hie_val in
    istore_ptr_offs res vp_ptr offs vp_val
      
and ccomp_exp_assgn_var (ctx: varctx) (res: instr_t list)
  (d2v_ptr: dvar2) (hils: hilab list) (hie_val: hiexp): instr_t list =
  let vp_ptr = ccomp_exp_var ctx d2v_ptr in
  let (res, offs) = ccomp_hilab_list ctx res hils in
  let (res, vp_val) = ccomp_exp ctx res hie_val in
    istore_var_offs res vp_ptr offs vp_val
      
(* ****** ****** *)

and ccomp_exp_freeat
  (ctx: varctx) (res: instr_t list) (hie: hiexp): instr_t list =
  let (res, vp) = ccomp_exp ctx res hie in ifreeptr res vp

(* ****** ****** *)
      
and ccomp_exp_lam_with_funlab (fl: funlab) (ctx: varctx)
  (prolog: instr_t list) (hips_arg: hipat list) (hie_body: hiexp)
  : function_t =
  let () = dvar2_level_inc () in
  let () = vartyp_set_push () in
  let () = funlab_list_push () in
  let loc = hie_body.hiexp_loc in
  let k_fail_opt = Some (CONTfunarg_fail fl) in
  let (ctx, res) = ccomp_funarg fl k_fail_opt ctx prolog hips_arg in
  let hit_body = hie_body.hiexp_type in
(*
  let () =
    P.fprintf stdout "ccomp_exp_lam_with_funlab: hit_body = %a\n"
      fprint_hityp hit_body in
*)
  let tmp_ret = tmpvar_ret_new hit_body in
(*
  let () =
    P.fprintf stdout "ccomp_exp_lam_with_funlab: tmp_ret = %a\n"
      fprint_tmpvar tmp_ret in
*)
  let res = ccomp_exp_with_tmpvar ctx res tmp_ret hie_body in
  let fls = funlab_list_pop () in
  let vts = vartyp_set_pop () in
  let level = dvar2_level_dec_and_get () in
  let () =
    let aux vt =
      let d2v = vt.vartyp_var in
	if d2v.dvar2_level < level then vartyp_set_add vt in
      VarTypSet.iter aux vts in
  let f_entry =
    function_store_add loc fl level vts fls tmp_ret (List.rev res) in
    f_entry
      
(* ****** ****** *)
      
and ccomp_exp_ptrof_ptr (ctx: varctx)
  (res: instr_t list) (hie_ptr: hiexp) (hils: hilab list)
  : instr_t list * valprim = begin
(*
  let () = begin
    P.fprintf stdout "ccomp_exp_ptrof_ptr: hie_ptr = %a\n" fprint_hiexp hie_ptr
  end in
*)
  let (res, vp_ptr) = ccomp_exp ctx res hie_ptr in
  let (res, offs) = ccomp_hilab_list ctx res hils in
  let vp_res = match offs with
    | _ :: _ -> valprim_ptrof_ptr_offs vp_ptr offs | [] -> vp_ptr in
    (res, vp_res)
end (* end of [ccomp_exp_ptrof_ptr] *)
      
and ccomp_exp_ptrof_var (ctx: varctx)
  (res: instr_t list) (d2v: dvar2) (hils: hilab list)
  : instr_t list * valprim = begin
  let vp = varctx_find ctx d2v in
  let vp_root =
    let d2v_level = d2v.dvar2_level in
      if 0 < d2v_level && d2v_level < dvar2_level_get () then
	let vt = { vartyp_var= d2v; vartyp_typ= vp.valprim_type } in
	let hit =
	  if dvar2_is_mutable d2v then
	    let s2e = type_of_dvar2_ptr d2v in hityp_nf (sexp2_tr_0 s2e)
	  else vp.valprim_type in
	  (vartyp_set_add vt; valprim_env vt hit)
      else vp in
  let (res, offs) = ccomp_hilab_list ctx res hils in
  let vp_res = match offs with
    | _ :: _ -> valprim_ptrof_var_offs vp_root offs
    | [] -> valprim_ptrof vp_root in
    (res, vp_res)
end (* end of [ccomp_exp_ptrof_var] *)
      
(* ****** ****** *)
      
and ccomp_exp_seq_with_tmpvar (ctx: varctx)
  (res: instr_t list) (tmp_res: tmpvar) (hies: hiexp list): instr_t list =
  let rec aux res hie1 = function
    | hie2 :: hies ->
	let tmp = tmpvar_new hityp_void in
	let res = ccomp_exp_with_tmpvar ctx res tmp hie1 in
	  aux res hie2 hies
    | [] -> ccomp_exp_with_tmpvar ctx res tmp_res hie1 in
    match hies with [] -> res | hie :: hies -> aux res hie hies
      
(* ****** ****** *)
      
and ccomp_exp_refarg (ctx: varctx)
  (res: instr_t list) (refval: int) (hie: hiexp)
  : instr_t list * valprim = begin
  match refval with
    | _ when refval = 0 -> ccomp_exp ctx res hie
    | _ -> begin match hie.hiexp_node with (* call-by-ref *)
      | HIEsel_ptr (hie_ptr, hils) ->
	  ccomp_exp_ptrof_ptr ctx res hie_ptr hils
      | HIEsel_var (d2v_ptr, hils) ->
	  ccomp_exp_ptrof_var ctx res d2v_ptr hils
      | HIEvar d2v_ptr ->
	  ccomp_exp_ptrof_var ctx res d2v_ptr []
      | _ -> begin
	  P.eprintf "%a: ccomp_exp_refarg: hie = %a\n"
	    Loc.fprint hie.hiexp_loc fprint_hiexp hie;
	  Err.abort ()
	end
      end (* end of [_] *)
end (* end of [ccomp_exp_refarg] *)
					     
(* ****** ****** *)
					     
and ccomp_exp_var (ctx: varctx) (d2v: dvar2): valprim =
  let vp = varctx_find ctx d2v in
  let d2v_level = d2v.dvar2_level in
(*
  let () = P.fprintf stdout "vp = %a\n" fprint_valprim vp in
  let () = P.fprintf stdout "(%a).dvar2_level = %i\n" fprint_dvar2 d2v d2v_level in
*)
    if 0 < d2v_level && d2v_level < dvar2_level_get () then
      begin match vp.valprim_node with
	| _ when valprim_is_const vp -> vp
	| VPclo (_, fl, ctx) -> (funlab_list_add fl; vp)
	| _ -> begin
	    let vt = { vartyp_var= d2v; vartyp_typ= vp.valprim_type } in
	    let hit = vp.valprim_type in
(*
	    let hit = vp.valprim_type in
	      if dvar2_is_mutable d2v then
		let s2e = type_of_dvar2_ptr d2v in hityp_nf (sexp2_tr_0 s2e)
	      else vp.valprim_type in
*)
	      (vartyp_set_add vt; valprim_env vt hit)
	  end
      end
    else vp

and ccomp_exp_while (ctx: varctx)
  (res: instr_t list) (hie_test: hiexp) (hie_body: hiexp): instr_t list =
  let blab = tmplab_new () and clab = tmplab_new () in
  let () = loopexnlabs_list_push blab clab in
  let (is_test, vp_test) = ccomp_exp ctx [] hie_test in
  let (is_body, vp_void) = ccomp_exp ctx [] hie_body in
  let () = loopexnlabs_list_pop () in
    iwhile res blab clab vp_test (List.rev is_test) (List.rev is_body)

(* ****** ****** *)

and ccomp_hilab (ctx: varctx)
  (res: instr_t list) (hil: hilab): instr_t list * offset_t =
  match hil.hilab_node with
    | HILind (hit_elt, hiess_ind) ->
	let hit_elt = hityp_nf hit_elt in
	let (res, vpss) = ccomp_exp_list_list ctx res hiess_ind in
	  (res, OFFind (vpss, hit_elt))
    | HILlab (l, hit_rec) ->
	let hit_rec = hityp_nf hit_rec in (res, OFFlab (l, hit_rec))

and ccomp_hilab_list (ctx: varctx)
  (res: instr_t list) (hils: hilab list): instr_t list * offset_t list =
  let rec aux res offs = function
    | hil :: hils ->
	let (res, off) = ccomp_hilab ctx res hil in
	  aux res (off :: offs) hils
    | [] -> (res, List.rev offs) in
    aux res [] hils

(* ****** ****** *)

and ccomp_hicla (k_fail_opt: cont_t option) (ctx: varctx)
  (tmp_res: tmpvar) (vps: valprim list) (hicl: hicla): instr_t list =
  let level = dvar2_level_get () in
  let () = freed_valprim_list_reset () in
  let (ctx, res) =
    ccomp_match_list level k_fail_opt ctx [] vps hicl.hicla_pat in
  let vps_free = freed_valprim_list_get () in
  let res = match k_fail_opt with
    | Some k_fail -> begin match hicl.hicla_gua with
	| Some hie_gua ->
	    let (res, vp) = ccomp_exp ctx res hie_gua in
	      ipatck res vp (PATCKbool true) k_fail
	| None -> res
      end
    | None -> res in
  let res = List.fold_left ifreeptr res vps_free in
  let res = ccomp_exp_with_tmpvar ctx res tmp_res hicl.hicla_body in
    List.rev res

and ccomp_hicla_list (k_fail_opt: cont_t option) (ctx: varctx)
  (tmp_root: tmpvar) (vps: valprim list) (hicls: hicla list): branch_t list =
  let rec aux l_self brs hicl hicls = match hicls with
    | hicl1 :: hicls1 ->
	let l_next = tmplab_new () in
	let k_fail = CONTtmplab l_next in
	let tmp_res = tmpvar_new_with_root tmp_root in
	let res = ccomp_hicla (Some k_fail) ctx tmp_res vps hicl in
	  aux l_next ((l_self, res) :: brs) hicl1 hicls1
    | [] -> begin
	let br = match k_fail_opt with
	  | Some k_fail ->
	      let tmp_res = tmpvar_new_with_root tmp_root in
	      let res = ccomp_hicla (Some k_fail) ctx tmp_res vps hicl in
		(l_self, res)
	  | None ->
	      let tmp_res = tmpvar_new_with_root tmp_root in
	      let res = ccomp_hicla None ctx tmp_res vps hicl in
		(l_self, res) in
	  List.rev (br :: brs)
      end in
  let l_first = tmplab_new () in match hicls with
    | hicl :: hicls -> aux l_first [] hicl hicls
    | [] -> begin
        let ins = Iextern "ats_caseof_failure_handle(\"GEIZELLA\")" in
	let br = (l_first, [ins]) in [br]
      end (* end of [] *)
(* end of [ccomp_hicla_list] *)

(* ****** ****** *)

and ccomp_dec
  (ctx: varctx) (res: instr_t list) (hid: hidec): varctx * instr_t list =
  match hid.hidec_node with
    | HIDextype (name, hit_def) ->
	let hit_def = hityp_nf hit_def in
        let () = extype_list_add name hit_def in
	  (ctx, res)
    | HIDextval (name, hie_def) ->
	let (res, vp_def) = ccomp_exp ctx res hie_def in
	let () = extval_list_add name vp_def in (ctx, res)
    | HIDdyncsts (dck, d2cs) ->
        let () =
          if not (Syn.dcstkind_is_proof dck) then
	    List.iter dyncst_set_add d2cs in
	  (ctx, res)
    | HIDdata (dtk, s2cs) ->
        let () =
          if not (Syn.datakind_is_proof dtk) then
	    List.iter sum_cst_set_add s2cs in
	  (ctx, res)
    | HIDimpls (ds: hidec_impl list) ->
	let res = ccomp_dec_impl_list ctx res ds in (ctx, res)
    | HIDfuns (is_temp, fk, ds) -> begin
	if is_temp then (ctx, res)
	else begin match ds with
	  | [_] -> let ctx = ccomp_dec_fun_list ctx ds in (ctx, res)
	  | _ when Syn.funkind_is_recursive_tail fk ->
	      let ctx = ccomp_dec_fnt_list hid.hidec_loc ctx ds in (ctx, res)
	  | _ -> let ctx = ccomp_dec_fun_list ctx ds in (ctx, res)
	end
      end
    | HIDvals (vk, (ds: hidec_val list)) ->
	let is_exhaustive = Syn.valkind_is_exhaustive vk in
	  ccomp_dec_val_list is_exhaustive ctx res ds

    | HIDvalpars (ds: hidec_val list) ->
	ccomp_dec_valpar_list ctx res ds

    | HIDvalrecs (ds: hidec_val list) ->
	ccomp_dec_valrec_list ctx res ds
    | HIDvars (is_stack, ds) -> ccomp_dec_var_list ctx res ds
    | HIDlocal (hids_head, hids_body) ->
	let (ctx, res) = ccomp_dec_list ctx res hids_head in
	  ccomp_dec_list ctx res hids_body
    | HIDstaload (filename, ohids) ->
	let () = stafile_list_add filename in (ctx, res)
    | HIDdynload filename ->
	let () = dynfile_list_add filename in
	let res = Iload_file filename :: res in (ctx, res)
    | HIDextern (pos, code) ->
	let () = extcode_list_add pos code in (ctx, res)

and ccomp_dec_list
  (ctx: varctx) (res: instr_t list) (ds: hidec list): varctx * instr_t list =
  let rec aux ctx res ds = match ds with
    | d :: ds -> let (ctx, res) = ccomp_dec ctx res d in aux ctx res ds
    | [] -> (ctx, res) in
    aux ctx res ds

and ccomp_dec_impl
  (ctx: varctx) (res: instr_t list) (d: hidec_impl): instr_t list =
  let rec aux ctx d2c hie = match hie.hiexp_node with
    | HIElam (hips_arg, hie_body) ->
	let fl = funlab_new_with_dcst2 d2c in
	let fcr = match hityp_funclo_get fl.funlab_type with
	  | Some fcr -> fcr
	  | None -> begin
	      error_of_deadcode "ats_ccomp_trans: ccomp_exp_template_cst: fcr"
	    end in
	let vp_lam = match fcr with
	  | Syn.FUNCLOclo i -> valprim_clo i fl ctx
	  | Syn.FUNCLOfun -> valprim_fun fl in
	let () = toplevel_cstctx_add d2c vp_lam in
	let () = tailjoin_list_push_mrk () in
	let () = tailjoin_list_push_lab fl [] in
	let prolog = [Ilabel_fun fl] in
	let _ (* function_t *) =
	  ccomp_exp_lam_with_funlab fl ctx prolog hips_arg hie_body in
	let () = tailjoin_list_pop () in
	  if dcst2_is_funcst d2c then res else begin
	    match fcr with
	      | Syn.FUNCLOclo _(*knd*) -> idefine_clo res d2c fl
	      | Syn.FUNCLOfun -> idefine_fun res d2c fl
	  end (* end of [if] *)
    | HIEfix (d2v_fix, hie_def) ->
	let hit = hie.hiexp_type in
	let ctx = varctx_add ctx d2v_fix (valprim_cst d2c hit) in
	  aux ctx d2c hie_def
    | _ when dcst2_is_funcst d2c -> begin
	P.eprintf
	  "%a: incorrect implementation for the constant function <%a>.\n"
	  Loc.fprint d.hidec_impl_loc fprint_dcst2 d2c;
	Err.abort ();
      end
    | _ -> begin
	let (res, vp) = ccomp_exp ctx res hie in
	let hit = vp.valprim_type in
	let () = match hit.hityp_node with
	  | HITfun (_, hits_arg, hit_res) -> 
	      function_store_add_cst_fun d2c hits_arg hit_res
	  | _ -> () in
	let () = toplevel_cstctx_add d2c vp in
	  idefine_val res d2c vp
      end in
    if d.hidec_impl_istemp then res else begin
      aux ctx d.hidec_impl_cst d.hidec_impl_def
    end

and ccomp_dec_impl_list
  (ctx: varctx) (res: instr_t list) (ds: hidec_impl list): instr_t list =
  let rec aux res ds = match ds with
    | d :: ds ->
	let res = ccomp_dec_impl ctx res d in aux res ds
    | [] -> res in
    aux res ds

(* ****** ****** *)

and ccomp_dec_fun_list_aux (level: int) (ctx: varctx)
  (ds: hidec_fun list): varctx * (dvar2 * funlab * hipat list * hiexp) list =
  let rec aux ctx d2v_fl_arg_body_list ds = match ds with
    | d :: ds ->
	let d2v_fun = d.hidec_fun_name in
	let () = d2v_fun.dvar2_level <- level in
(*
	let () =
	  P.fprintf stdout "(%a).dvar2_level = %i" fprint_dvar2 d2v_fun level in
*)
	let fl = funlab_new_with_dvar2 d2v_fun in
	let fcr = match hityp_funclo_get fl.funlab_type with
	  | Some fcr -> fcr
	  | None -> begin
	      error_of_deadcode "ats_ccomp_trans: ccomp_dec_fun_list_aux: fcr"
	    end in
	let vp_lam = match fcr with
	  | Syn.FUNCLOclo i -> valprim_clo i fl ctx
	  | Syn.FUNCLOfun -> valprim_fun fl in
	let ctx = varctx_add ctx d2v_fun vp_lam in
	let fl_arg_body_list =
	  let hie_def = d.hidec_fun_def in
	    match hie_def.hiexp_node with
	      | HIElam (hips_arg, hie_body) ->
		  (d2v_fun, fl, hips_arg, hie_body) :: d2v_fl_arg_body_list
	      | _ -> error_of_deadcode "ats_ccomp_trans: ccomp_dec_fun" in
	  aux ctx fl_arg_body_list ds
    | [] -> (ctx, List.rev d2v_fl_arg_body_list) in
    aux ctx [] ds

and ccomp_dec_fun_list (ctx: varctx) (ds: hidec_fun list): varctx =
  let level = dvar2_level_get () in
  let (ctx, d2v_fl_arg_body_list) = ccomp_dec_fun_list_aux level ctx ds in
  let aux (d2v_fun, fl, hips_arg, hie_body) =
    let () = tailjoin_list_push_mrk () in
    let () = tailjoin_list_push_lab fl [] in
    let prolog = [Ilabel_fun fl] in
    let _ (* function_t *) =
      ccomp_exp_lam_with_funlab fl ctx prolog hips_arg hie_body in
    let () = tailjoin_list_pop () in () in
    (List.iter aux d2v_fl_arg_body_list; ctx)

(* ****** ****** *)

and ccomp_dec_fnt_list loc (ctx: varctx) (ds: hidec_fun list): varctx =
  let level = dvar2_level_get () in
  let (ctx, d2v_fl_arg_body_list) = ccomp_dec_fun_list_aux level ctx ds in
  let () = tailjoin_list_push_mrk () in
  let () = (* push *)
    let aux_push (d2v_fun, fl, hips_arg, hie_body) =
      let tmps_arg =
	List.map (function hip -> tmpvar_new (hip.hipat_type)) hips_arg in
      let () = fl.funlab_tailjoined <- tmps_arg in
      tailjoin_list_push_lab fl tmps_arg in
      List.iter aux_push d2v_fl_arg_body_list in
  let fs = (* compile *)
    let aux_ccomp (d2v_fun, fl, hips_arg, hie_body): function_t =
      let prolog = [Ilabel_fun fl] in
	ccomp_exp_lam_with_funlab fl ctx prolog hips_arg hie_body in
      List.map aux_ccomp d2v_fl_arg_body_list in
  let () = tailjoin_list_pop () in
    (function_list_tailjoin loc ctx fs; ctx)

(* ****** ****** *)

and ccomp_dec_val (is_exhaustive: bool) (level: int)
  (ctx: varctx) (res: instr_t list) (d: hidec_val): varctx * instr_t list =
  let (res, vp) = ccomp_exp ctx res d.hidec_val_def in
  let k_fail_opt =
    if is_exhaustive then None else Some (CONTmatch_fail) in
  let () = freed_valprim_list_reset () in
  let (ctx, res) =
    ccomp_match level k_fail_opt ctx res vp d.hidec_val_pat in
  let vps_free = freed_valprim_list_get () in
  let res = List.fold_left ifreeptr res vps_free in
    (ctx, res)

and ccomp_dec_val_list (is_exhaustive: bool)
  (ctx: varctx) (res: instr_t list) (ds: hidec_val list): varctx * instr_t list =
  let level = dvar2_level_get () in
  let rec aux ctx res ds = match ds with
    | d :: ds ->
	let (ctx, res) = ccomp_dec_val is_exhaustive level ctx res d in
	  aux ctx res ds
    | [] -> (ctx, res) in
    aux ctx res ds

and ccomp_dec_valpar_list (ctx: varctx) (res: instr_t list)
  (ds: hidec_val list): varctx * instr_t list = begin
  let level = dvar2_level_get () in
  let ttvs: (tmpvar * tmpvar * valprim) list =
    let f (d: hidec_val): tmpvar * tmpvar * valprim =
      let hie_def = d.hidec_val_def in
      let loc_def = hie_def.hiexp_loc in
      let hit_def = hie_def.hiexp_type in
      let d2v_res =
	let d2v = dvar2_new loc_def false(*is_fixed*) in
	let d2v_view = dvar2_new loc_def false(*is_fixed*) in
	let () = d2v.dvar2_view <- Some d2v_view in
	let () = d2v.dvar2_level <- level in d2v in
      let tmp_res = tmpvar_mut_new hit_def in
      let ctx = varctx_add ctx d2v_res (valprim_tmp tmp_res) in
      let tmp_ret = tmpvar_new hityp_ptr in
      let vp_clo =
	let hie_body =
	  if hityp_is_void hit_def then hie_def
	  else begin
	    hiexp_assgn_var loc_def hityp_void d2v_res [] hie_def
	  end in
	  ccomp_exp_thunk ctx hie_body in
	(tmp_res, tmp_ret, vp_clo) in
      List.map f ds in
  let rec aux_spawn
    (res: instr_t list) (ttvs: (tmpvar * tmpvar * valprim) list): instr_t list =
    match ttvs with
      | (tmp_res, tmp_ret, vp_clo) :: ttvs ->
	  let res = ivardec res tmp_res in
	  let res = iparallel_spawn res tmp_ret vp_clo in
	    aux_spawn res ttvs
      | [] -> res in
  let res = aux_spawn res ttvs in
  let rec aux_sync
    (res: instr_t list) (ttvs: (tmpvar * tmpvar * valprim) list): instr_t list =
    match ttvs with
      | (_(*tmp_res*), tmp_ret, _(*vp_clo*)) :: ttvs ->
	  let res = iparallel_sync res tmp_ret in aux_sync res ttvs
      | [] -> res in
  let res = aux_sync res ttvs in
  let rec aux_match (ctx: varctx) (res: instr_t list)
    (ttvs: (tmpvar * tmpvar * valprim) list) (ds: hidec_val list)
    : varctx * instr_t list =
    match ds, ttvs with
      | d :: ds, (tmp_res, _(*tmp_ret*), _(*vp_clo*)) :: ttvs ->
	  let vp = valprim_tmp tmp_res in
	  let k_fail_opt = None in
	  let (ctx, res) =
	    ccomp_match level k_fail_opt ctx res vp d.hidec_val_pat in
	    aux_match ctx res ttvs ds
      | _, _ (* [], [] *) -> (ctx, res) in
    aux_match ctx res ttvs ds
end (* end of [ccomp_dec_valpar_list] *)

and ccomp_dec_valrec_list
  (ctx: varctx) (res: instr_t list) (ds: hidec_val list): varctx * instr_t list =
  let level = dvar2_level_get () in
  let rec aux1 deftmps ctx res = function
    | d :: ds ->
	let def = d.hidec_val_def in
	let hit_def = def.hiexp_type in
	let tmp = tmpvar_new hit_def in
	let vp = valprim_tmp tmp in
	let (ctx, res) = ccomp_match level None ctx res vp d.hidec_val_pat in
	  aux1 ((def, tmp) :: deftmps) ctx res ds
    | [] -> (ctx, res, List.rev deftmps) in
  let rec aux2 ctx res deftmps = match deftmps with
    | (def, tmp) :: deftmps ->
	let res = ccomp_exp_with_tmpvar ctx res tmp def in
	  aux2 ctx res deftmps
    | [] -> (ctx, res) in
  let (ctx, res, deftmps) = aux1 [] ctx res ds in
    aux2 ctx res deftmps
(* end of [ccomp_dec_valrec_list] *)

(* ****** ****** *)

and ccomp_dec_var_list 
  (ctx: varctx) (res: instr_t list) (ds: hidec_var list): varctx * instr_t list =
  let level = dvar2_level_get () in
  let rec aux ctx res ds = match ds with
    | d :: ds ->
	let d2v_ptr = d.hidec_var_ptr in
	let () = d2v_ptr.dvar2_level <- level in
	let hit = sexp2_tr_0 (type_of_dvar2_ptr d2v_ptr) in
	let tmp = tmpvar_mut_new hit in
	let ctx = varctx_add ctx d2v_ptr (valprim_tmp tmp) in
	let res = match d.hidec_var_ini with
	  | Some hie_ini -> ccomp_exp_with_tmpvar ctx res tmp hie_ini
	  | None -> ivardec res tmp in
	  aux ctx res ds
    | [] -> (ctx, res) in
    aux ctx res ds
(* end of [ccomp_dec_var_list] *)

(* ****** ****** *)

(* end of [ats_ccomp_trans.ml] *)
