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

open Ats_hiexp
open Ats_hiexp_util
open Ats_trans4

open Ats_ccomp

(* ****** ****** *)

module P = Printf

module Cnt = Ats_counter
module Eff = Ats_effect
module Fil = Ats_filename
module Lab = Ats_label
module Sym = Ats_symbol
module Syn = Ats_syntax

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_ccomp_util: "; Err.error s;
end

(* ****** ****** *)

let template_name
  (base: string) (hitss: hityp list list): string =
  let sb = Buffer.create 256 in
  let () = Buffer.add_string sb base in
  let aux hit =
    let hit = hityp_nf hit in
    let name = name_of_hityp hit in
    (Buffer.add_char sb '_'; Buffer.add_string sb name) in
  let aux_list hits =
    (Buffer.add_char sb '_'; List.iter aux hits) in
  let () = List.iter aux_list hitss in Buffer.contents sb

(* ****** ****** *)

let template_bind
  (decarg: (svar2 list * sexp2 list) list) (hitss: hityp list list):
  (svar2 * hityp) list =
  let rec aux res s2vs hits = match s2vs, hits with
    | s2v :: s2vs, hit :: hits -> begin
	let hit = hityp_nf hit in aux ((s2v, hit) :: res) s2vs hits
      end
    | _, _ -> res in
  let rec aux_list res xys hitss = match xys, hitss with
    | (s2vs, s2es) :: xys, hits :: hitss ->
	let res = aux res s2vs hits in aux_list res xys hitss
    | _, _ -> res in
    aux_list [] decarg hitss

(* ****** ****** *)

let tmp_root (tmp: tmpvar): tmpvar =
  match tmp.tmpvar_root with Some tmp -> tmp | _ -> tmp

let tmpset_of_instr_list (res: instr_t list): TmpVarSet.t =
  let rec aux_instr tmps i = match i with
    | Iarray (tmp, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Icall (tmp, _, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Icond (_, res_then, res_else) ->
	let tmps = aux_instr_list tmps res_then in
	  aux_instr_list tmps res_else
    | Ifunction (tmp, vps_arg, res_body, tmp_ret) ->
	let tmps = TmpVarSet.add (tmp_root tmp) tmps in
	let tmps = TmpVarSet.add tmp_ret tmps in
	  aux_instr_list tmps res_body
    | Iload_ptr (tmp, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Iload_ptr_offs (tmp, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Iload_var (tmp, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Iload_var_offs (tmp, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Imove_con (tmp, _, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Imove_rec_box (tmp, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Imove_rec_flt (tmp, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Imove_val (tmp, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Ioper (tmp, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Iparallel_spawn (tmp, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Irefval (tmp, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Iselcon (tmp, _, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Iselcon_ptr (tmp, _, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Iselect (tmp, _, _) -> TmpVarSet.add (tmp_root tmp) tmps
    | Iswitch brs -> aux_branch_list tmps brs
    | Itrywith (res_try, tmp, brs) ->
	let tmps = aux_instr_list tmps res_try in
	let tmps = TmpVarSet.add (tmp_root tmp) tmps in
	  aux_branch_list tmps brs
    | Iwhile (_, _, _, res_test, res_body) ->
	let tmps = aux_instr_list tmps res_test in
	  aux_instr_list tmps res_body
    | Ivardec tmp -> TmpVarSet.add tmp tmps
    | _ -> tmps

  and aux_instr_list tmps is = List.fold_left aux_instr tmps is

  and aux_branch tmps (br_lab, br_body) = aux_instr_list tmps br_body

  and aux_branch_list tmps brs = List.fold_left aux_branch tmps brs in
    aux_instr_list TmpVarSet.empty res

let tmpset_of_function (f: function_t): TmpVarSet.t =
  let aux tmpset (tag, fl, tmps) =
    List.fold_left (fun tmpset tmp -> TmpVarSet.add tmp tmpset) tmpset tmps in
  let tmpset = tmpset_of_instr_list f.function_body in
    List.fold_left aux tmpset f.function_tailjoin

(* ****** ****** *)

let the_funarg_list: (valprim list) ref = ref []
let funarg_list_set (vps: valprim list): unit = the_funarg_list := vps
let funarg_list_reset (): unit = the_funarg_list := []

let funarg_list_find (i: int): valprim option =
  let rec aux i = function
    | vp :: vps -> if i > 0 then aux (i-1) vps else Some vp
    | [] -> None in
    aux i !the_funarg_list
(* end of [funarg_list_find] *)

(* ****** ****** *)

let hiexp_app_proc (ctx: varctx) (res: instr_t list) (hie: hiexp)
  : varctx * instr_t list * hiexp * valprim option = begin
  match hie.hiexp_node with
    | HIErefarg (refval, freeknd, hie_arg) when freeknd > 0 -> begin
	let loc = hie.hiexp_loc in
	let hit = hie.hiexp_type in
	let level = dvar2_level_get () in
	let d2v_res =
	  let d2v = dvar2_new loc false(*is_fixed*) in
	  let d2v_view = dvar2_new loc false(*is_fixed*) in
	  let () = d2v.dvar2_view <- Some d2v_view in
	  let () = d2v.dvar2_level <- level in d2v in
	let tmp_res = tmpvar_mut_new hit in
	let vp_res = valprim_tmp tmp_res in
	let ctx = varctx_add ctx d2v_res vp_res in
	let res = ivardec res tmp_res in
	let hie_assgn =
	  hiexp_assgn_var loc hityp_void d2v_res [] hie_arg in
	let hie_var = hiexp_var loc hit d2v_res in
	let hie_res = hiexp_refarg loc hit refval freeknd hie_var in
	let hie_seq = hiexp_seq loc hit [hie_assgn; hie_res] in
	  (ctx, res, hie_seq, Some vp_res)
      end (* end of [HIErefarg] *)
    | _ -> (ctx, res, hie, None)
end (* end of [hiexp_app_proc] *)

let rec hiexp_app_list_proc (ctx: varctx) (res: instr_t list)
  (hies: hiexp list): varctx * instr_t list * hiexp list * valprim list =
begin match hies with
  | hie :: hies -> begin
      let (ctx, res, hie, ovp) = hiexp_app_proc ctx res hie in
      let (ctx, res, hies, vps) = hiexp_app_list_proc ctx res hies in
      let hies = hie :: hies in
      let vps = match ovp with Some vp -> vp :: vps | None -> vps in
	(ctx, res, hies, vps)
    end (* end of [::] *)
  | [] -> (ctx, res, [], [])
end (* end of [hiexp_app_list_proc] *)

(* ****** ****** *)

(* end of [ats_ccomp_util.ml] *)
