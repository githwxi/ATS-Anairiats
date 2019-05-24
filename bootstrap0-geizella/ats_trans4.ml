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
open Ats_dyncst2
open Ats_dynexp2_util
open Ats_dynexp3

open Ats_hiexp
open Ats_hiexp_util

module P = Printf
module H = Hashtbl

module Fil = Ats_filename
module Lab = Ats_label
module Loc = Ats_location

(* ****** ****** *)

type lab = Lab.label
type labstring = lab * string
type loc = Loc.location

(* ****** ****** *)

let the_typedef_cnt: int ref = ref 0
let the_typedef_base: string ref = ref ""
let typedef_base_set (base: string): unit =
  the_typedef_base := base

(* ****** ****** *)

type tykey =
  | TYKEYrec of labstring list
  | TYKEYsum of int * string list
  | TYKEYuni of labstring list

let the_typedef_list: (tykey * string) list ref = ref []
let typedef_list_add (tk: tykey) (name: string): unit =
  the_typedef_list := (tk, name) :: !the_typedef_list
let typedef_list_get (): (tykey * string) list =
  List.rev (!the_typedef_list)
let typedef_list_reset (): unit = the_typedef_list := []

(* key: labsexp2 list *)
let the_typedef_map: (tykey, string) H.t = H.create 0
let typedef_map_reset () = H.clear the_typedef_map

(* ****** ****** *)

let typedef_map_add_rec (tk: tykey): string =
  let n = !the_typedef_cnt in
  let () = the_typedef_cnt := n+1 in
  let name_rec = P.sprintf "%s_rec_%i" !the_typedef_base n in
  let () = H.add the_typedef_map tk name_rec in
  let () = typedef_list_add tk name_rec in
    name_rec
(* end of [typedef_map_add_rec] *)

let typedef_map_add_sum (tk: tykey): string =
  let n = !the_typedef_cnt in
  let () = the_typedef_cnt := n+1 in
  let name_sum = P.sprintf "%s_sum_%i" !the_typedef_base n in
  let () = H.add the_typedef_map tk name_sum in
  let () = typedef_list_add tk name_sum in
    name_sum
(* end of [typedef_map_add_sum] *)

let typedef_map_add_uni (tk: tykey): string =
  let n = !the_typedef_cnt in
  let () = the_typedef_cnt := n+1 in
  let name_uni = P.sprintf "%s_uni_%i" !the_typedef_base n in
  let () = H.add the_typedef_map tk name_uni in
  let () = typedef_list_add tk name_uni in
    name_uni
(* end of [typedef_map_add_uni] *)

let typedef_map_find (tk: tykey): string =
  try H.find the_typedef_map tk with Not_found -> begin
    match tk with
      | TYKEYrec _ -> typedef_map_add_rec tk
      | TYKEYsum _ -> typedef_map_add_sum tk
      | TYKEYuni _ -> typedef_map_add_uni tk
  end
(* end of [typedef_map_find] *)

(* ****** ****** *)

let hityp_sum_make (d2c: dcon2) (hits_arg: hityp list): hityp =
  match hits_arg with
    | [] -> hityp_sum_ptr
    | _ -> begin
(*
	let () =
	  P.fprintf stdout "hityp_sum_make: d2c = %a\n"
	    fprint_dcon2 d2c in
	let () =
	  P.fprintf stdout "hityp_sum_make: hits_arg = %a\n"
	    fprint_hityp_list hits_arg in
*)
	let names_arg = List.map name_of_hityp hits_arg in
	let tag = match d2c with
	  | _ when dcon2_is_singular d2c -> 0
	  | _ when dcon2_is_list_like d2c -> 0
	  | _ when dcon2_is_exn d2c -> -1
	  | _ -> 1 in
	let tk = TYKEYsum (tag, names_arg) in
	let name_sum = typedef_map_find tk in
	  { hityp_name= HITNAM_ptr name_sum; hityp_node= HITsum (d2c, hits_arg); }
      end
(* end of [hityp_sum_make] *)

let hityp_tyrec_make (is_flat: bool) (lhits: labhityp list): hityp =
  let lnames = List.map labname_of_labhityp lhits in
  let tk = TYKEYrec lnames in
  let name_rec = typedef_map_find tk in
(*
  let () =
    P.fprintf stdout "hityp_tyrec_make: TYRECflt: name_rec = %s\n"
      name_rec in
*)
    if is_flat then
      hityp_tyrec_flt name_rec lhits
    else
      hityp_tyrec_box name_rec lhits
(* end of [hityp_tyrec_make] *)

(* ****** ****** *)

let rec hityp_nf (hit: hityp): hityp =
(*
  let () =
    P.fprintf stdout "hityp_nf = %a\n" fprint_hityp hit in
*)
  match hit.hityp_node with
    | HITvar s2v -> begin
	let hit_opt = svar2_hityp_list_find s2v in
	  match hit_opt with Some hit -> hit | None -> hit
      end
    | HITfun (ft, hits_arg, hit_res) ->
	let hits_arg = hityp_list_nf hits_arg in
	let hit_res = hityp_nf hit_res in
	  hityp_fun ft hits_arg hit_res
    | HITsum_tmp (d2c, hits_arg) ->
	let hits_arg = hityp_list_nf hits_arg in
	  hityp_sum_make d2c hits_arg
    | HITtyrec_box_tmp (lhits_arg) ->
	let lhits_arg = labhityp_list_nf lhits_arg in
	  hityp_tyrec_make false (*is_flat*) lhits_arg
    | HITtyrec_flt_tmp (lhits_arg) ->
	let lhits_arg = labhityp_list_nf lhits_arg in
	  hityp_tyrec_make true (*is_flat*) lhits_arg
    | _ -> hit
(* end of [hityp_nf] *)

and hityp_list_nf (hits: hityp list): hityp list =
  match hits with
    | hit :: hits -> hityp_nf hit  :: hityp_list_nf hits
    | [] -> []
(* end of [hityp_list_nf] *)

and labhityp_list_nf (lhits: labhityp list): labhityp list =
  match lhits with
    | (l, hit) :: lhits ->
	(l, hityp_nf hit)  :: labhityp_list_nf lhits
    | [] -> []
(* end of [labhityp_list_nf] *)

(* ****** ****** *)

let rec sexp2_tr (is_deep: int) (s2e0: sexp2): hityp =
(*
  let () =
    P.fprintf stdout "sexp2_tr: s2e0 = %a\n" fprint_sexp2 s2e0 in
*)
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2app (s2e_fun, s2es_arg) ->
	sexp2_app_tr is_deep s2e0.sexp2_sort s2e_fun s2es_arg
    | SE2clo (knd, s2e_fun) -> begin
	if is_deep > 0 then
	  let fc = Syn.FUNCLOclo knd in sexp2_fun_tr is_deep fc s2e_fun
	else begin
          if knd = 0 then hityp_abs else hityp_ptr
        end
      end
    | SE2cst s2c -> begin match s2c.scst2_isabs with
	| Some (Some s2e) -> sexp2_tr is_deep s2e
	| _ -> begin
	    if srt2_is_boxed s2e0.sexp2_sort then hityp_ptr else hityp_abs
	  end
      end
    | SE2datcon _ -> hityp_ptr
    | SE2datuni _ -> hityp_ptr
    | SE2exi (s2vs, s2ps, s2e) -> sexp2_tr is_deep s2e
    | SE2extype name -> hityp_extype name
    | SE2fun _ -> begin
	if is_deep > 0 then sexp2_fun_tr is_deep (Syn.FUNCLOfun) s2e0
	else hityp_ptr
      end
    | SE2mfun (ostamp, s2es_met, s2e) -> sexp2_tr is_deep s2e
    | SE2refarg (refval, s2e_in, s2e_out) -> begin
	let hit_in = sexp2_tr 0 s2e_in in
	  if refval = 0 then hit_in
	  else begin
	    let hit_out = sexp2_tr 0 s2e_out in
	      hityp_refarg refval hit_in hit_out
	  end
      end (* end of SE2refarg *)
    | SE2top s2e -> sexp2_tr 0 s2e
    | SE2tyarr (s2e_elt, s2ess_dim) ->
	hityp_tyarr (sexp2_tr 0 s2e_elt) s2ess_dim
    | SE2tyrec (k, (npf, ls2es)) -> begin
(*
	let () =
	  P.fprintf stdout "sexp2_tr: SE2tyrec: ls2es = %a\n"
	    fprint_labsexp2_list ls2es in
*)
	let lhits = labsexp2_list_tr npf ls2es in match k with
	  | TYRECbox ->
	      if is_deep > 0 then hityp_tyrec_box_tmp lhits
	      else hityp_ptr
	  | _ -> begin match lhits with
	      | [l, hit] -> hityp_tyrec_sin hit
	      | _ -> hityp_tyrec_flt_tmp lhits
	    end
      end
    | SE2uni (s2vs, s2ps, s2e) -> sexp2_tr is_deep s2e
    | SE2union (s2i, ls2es) -> begin
	let lhits = labsexp2_list_tr 0 ls2es in
	let lnames = List.map labname_of_labhityp lhits in
	let tk = TYKEYuni lnames in
	let name_uni = typedef_map_find tk in
	  hityp_union name_uni lhits
      end
    | SE2Var s2V -> sVar2_tr is_deep s2V
    | SE2VarApp (s2V, _) -> sVar2_tr is_deep s2V
    | SE2var s2v -> hityp_var s2v
    | SE2vararg _ -> hityp_vararg
    | _ -> begin
	P.eprintf "sexp2_tr: s2e0 = %a\n" fprint_sexp2 s2e0;
	Err.abort ();
      end
(* end of [sexp2_tr] *)

(* ****** ****** *)

and sexp2_app_tr (is_deep: int)
  (s2t_app: srt2) (s2e_fun: sexp2) (s2es_arg: sexp2 list): hityp =
  match s2e_fun.sexp2_node with
    | SE2cst s2c -> begin match s2c.scst2_isabs with
	| Some (Some s2e_fun) -> begin match s2e_fun.sexp2_node with
	    | SE2lam (s2vs_arg, s2e_body) -> begin
		let sub = sexp2_list_bind Loc.nonloc s2vs_arg s2es_arg in
		let s2e_app = sexp2_subst sub s2e_body in
		  sexp2_tr is_deep s2e_app
	      end
	    | _ -> error_of_deadcode "ats_trans4: sexp2_app_tr"
	  end
	| _ -> if srt2_is_boxed s2t_app then hityp_ptr else hityp_abs
      end
    | _ -> if srt2_is_boxed s2t_app then hityp_ptr else hityp_abs
(* end of [sexp2_app_tr] *)


and sexp2_fun_tr
  (is_deep: int) (fc: Syn.funclo) (s2e_fun: sexp2): hityp = begin
  match s2e_fun.sexp2_node with
    | SE2fun (_(*lin*), _(*sf2e*), (npf, s2es_arg), s2e_res) -> begin
	if is_deep > 0 then
	  let hits_arg = sexp2_list_tr npf s2es_arg in
	  let hit_res = sexp2_tr 0 s2e_res in
	    hityp_fun fc hits_arg hit_res
	else hityp_ptr
      end
    | _ -> begin
	P.eprintf "sexp2_fun_tr: is_deep = %i\n" is_deep;
	P.eprintf "sexp2_fun_tr: s2e_fun = %a\n" fprint_sexp2 s2e_fun;
	Err.abort ()
      end
end (* end of [sexp2_fun_tr] *)

(* ****** ****** *)

and sVar2_tr (is_deep: int) (s2V: sVar2): hityp =
  match s2V.sVar2_lbs with
    | s2e :: _ -> sexp2_tr is_deep s2e
    | [] -> begin match s2V.sVar2_ubs with
	| s2e :: _ -> sexp2_tr is_deep s2e
	| [] -> begin
	    P.eprintf "%a: ats_trans4: sVar2_tr: %a\n"
	      Loc.fprint s2V.sVar2_loc fprint_sVar2 s2V;
	    Err.abort ();
	  end
      end
(* end of [sVar2_tr] *)

(* ****** ****** *)

and sexp2_list_tr (npf: int) (s2es: sexp2 list): hityp list =
  let rec aux1 = function
    | s2e :: s2es ->
	if sexp2_is_proof s2e then aux1 s2es
	else (sexp2_tr 0 s2e) :: aux1 s2es
    | [] -> [] in
  let rec aux2 i s2es =
    if i < npf then match s2es with
      | s2e :: s2es -> aux2 (i+1) s2es
      | [] -> []
    else aux1 s2es in
    aux2 0 s2es
(* end of [sexp2_list_tr] *)

and labsexp2_list_tr (npf: int) (ls2es: labsexp2 list): labhityp list =
  let rec aux1 = function
    | (l, s2e) :: ls2es ->
	if sexp2_is_proof s2e then begin
	  aux1 ls2es
	end else begin
	  (l, sexp2_tr 0 s2e) :: aux1 ls2es
	end
    | [] -> [] in
  let rec aux2 i ls2es =
    if i < npf then match ls2es with
      | ls2e :: ls2es -> aux2 (i+1) ls2es
      | [] -> []
    else aux1 ls2es in
    aux2 0 ls2es
(* end of [labsexp2_list_tr] *)

(* ****** ****** *)

let sexp2_tr_0 = sexp2_tr 0
let sexp2_tr_1 = sexp2_tr 1

(* ****** ****** *)

(* declared but not used *)
let the_exn_con_set: (DconSet.t) ref = ref (DconSet.empty)
let exn_con_set_get (): DconSet.t = !the_exn_con_set
let exn_con_set_add (d2c: dcon2): unit =
  the_exn_con_set := DconSet.add d2c !the_exn_con_set

(* ****** ****** *)

(* for compiling templates *)

let tempdef_cst_tbl_size_hint = 1024
let the_tempdef_cst_tbl : (string, decarg2 * hiexp) H.t =
  H.create tempdef_cst_tbl_size_hint
let tempdef_cst_tbl_add
  (d2c: dcst2) (decarg: decarg2) (hie: hiexp): unit =
  let key = d2c.dcst2_fullname_id in
    H.add the_tempdef_cst_tbl key (decarg, hie)
let tempdef_cst_tbl_find (d2c: dcst2): (decarg2 * hiexp) option =
  let key = d2c.dcst2_fullname_id in
  try Some (H.find the_tempdef_cst_tbl key) with Not_found -> None
let tempdef_cst_tbl_clear (): unit = H.clear the_tempdef_cst_tbl

let the_tempdef_var_map : (hiexp DvarMap.t) ref =
  ref (DvarMap.empty)
let tempdef_var_map_add (d2v: dvar2) (hie: hiexp): unit =
  the_tempdef_var_map := DvarMap.add d2v hie !the_tempdef_var_map
let tempdef_var_map_find (d2v: dvar2): hiexp option =
  try Some (DvarMap.find d2v !the_tempdef_var_map)
  with Not_found -> None
let tempdef_var_map_reset (): unit =
  the_tempdef_var_map := DvarMap.empty

(* ****** ****** *)

let rec pat3_tr (p3t0: pat3): hipat =
  let loc0 = p3t0.pat3_loc in
  let hit0 = sexp2_tr_0 p3t0.pat3_type in
(*
  let () = P.fprintf stdout "pat3_tr: p3t0 = %a\n" fprint_pat3 p3t0 in
  let () = P.fprintf stdout "pat3_tr: hit0 = %a\n" fprint_hityp hit0 in
*)
    match p3t0.pat3_node with
      | PT3any _ -> hipat_any loc0 hit0
      | PT3bool b -> hipat_bool loc0 hit0 b
      | PT3char c -> hipat_char loc0 hit0 c
      | PT3con (freeknd, d2c, (npf, p3ts_arg)) ->
	  let hips_arg = pat3_arg_list_tr npf p3ts_arg in
	  let hits_arg = List.map (function hip -> hip.hipat_type) hips_arg in
(*
	  let () =
	    P.fprintf stdout "pat3_tr: PT3con: hits_arg = %a\n"
	      fprint_hityp_list hits_arg in
*)
	  let hit_sum = hityp_sum_tmp d2c hits_arg in
(*
	  let () = 
	    P.fprintf stdout "pat3_tr: PT3con: hit_sum = %a\n"
	      fprint_hityp hit_sum in
*)
	    hipat_con loc0 hit0 freeknd hit_sum d2c hips_arg
      | PT3empty -> hipat_empty loc0 hit0
      | PT3int i -> hipat_int loc0 hit0 i
      | PT3lst p3ts ->
	  let hips = pat3_list_tr p3ts in hipat_lst loc0 hit0 hips
      | PT3rec (is_flat, (npf, lp3ts)) ->
	  let hit_rec = sexp2_tr_1 p3t0.pat3_type in
	  let lhips = labpat3_arg_list_tr npf lp3ts in
	    hipat_rec loc0 hit0 is_flat hit_rec lhips
      | PT3string s -> hipat_string loc0 hit0 s
      | PT3var (isref, d2v, op3t) ->
	  let ohip = match op3t with
	    | Some p2t -> Some (pat3_tr p2t) | None -> None in
(*
          let s2e = match d2v.dvar2_type with
	    | None -> error_of_deadcode "pat3_tr: PT3var"
            | Some s2e -> s2e in
          let () =
	    P.fprintf stdout
	      "pat3_tr: PT3var: d2v.type = %a\n" fprint_sexp2 s2e in
*)
	  hipat_var loc0 hit0 isref d2v ohip
      | PT3vbox d2v -> error_of_deadcode "ats_trans4: pat3_tr"
(* end of [pat3_tr] *)

and pat3_arg_list_tr
  (npf: int) (p3ts: pat3 list): hipat list =
  let rec aux i p3ts = match p3ts with
    | p3t :: p3ts ->
	if i < npf then aux (i+1) p3ts
	else if pat3_is_proof p3t then aux (i+1) p3ts
	else pat3_tr p3t :: aux (i+1) p3ts
    | [] -> [] in
    aux 0 p3ts
(* end of [pat3_arg_list_tr] *)

and pat3_list_tr (p3ts: pat3 list): hipat list =
  List.map pat3_tr p3ts

and labpat3_arg_list_tr
  (npf: int) (lp3ts: labpat3 list): labhipat list =
  let rec aux i lp3ts = match lp3ts with
    | (l, p3t) :: lp3ts ->
	if i < npf then aux (i+1) lp3ts
	else if pat3_is_proof p3t then aux (i+1) lp3ts
	else (l, pat3_tr p3t) :: aux (i+1) lp3ts
    | [] -> [] in
    aux 0 lp3ts
(* end of [labpat3_arg_list_tr] *)

(* ****** ****** *)

let rec dexp3_tr (d3e0: dexp3): hiexp =
  let loc0 = d3e0.dexp3_loc in
  let s2e0 = d3e0.dexp3_type in
  let hit0 = sexp2_tr_0 s2e0 in
(*
  let () = P.fprintf stdout "dexp3_tr: s2e0 = %a\n" fprint_sexp2 s2e0 in
  let () = P.fprintf stdout "dexp3_tr: d3e0 = %a\n" fprint_dexp3 d3e0 in
*)
    match d3e0.dexp3_node with
      | DE3app_dyn (d3e_fun, (npf, d3es_arg)) -> begin
          let s2e_fun = d3e_fun.dexp3_type in
(*
	  let () = begin
	    P.fprintf stdout "dexp3_tr: DE3app_dyn: s2e_fun = %a\n" fprint_sexp2 s2e_fun
	  end in
*)
	  let hit_fun = sexp2_tr_1 s2e_fun in
	  let hie_fun = dexp3_tr d3e_fun in
	  let is_vararg = hityp_fun_is_vararg hit_fun in
	  let hies_arg = dexp3_fun_arg_list_tr is_vararg npf d3es_arg in
            match hie_fun.hiexp_node with
            | HIEcst d2c when dcst2_is_castfn d2c -> begin
              match hies_arg with
              | hie_arg :: _ -> hiexp_castfn loc0 hit0 d2c hie_arg
              | _ -> begin
                  P.fprintf stderr "%a: dexp3_tr: castfn: no argument.\n"
                    Loc.fprint loc0;
                  Err.abort ();
                end (* end of [_] *)
              end (* end of [HIEcst when ...] *)
	    | _ -> hiexp_app loc0 hit0 hit_fun hie_fun hies_arg
	end (* end of [DE3app_dyn] *)
      | DE3app_sta d3e -> dexp3_tr d3e
      | DE3arr (s2e_elt, d3es_elt) ->
	  let hit_elt = sexp2_tr_0 s2e_elt in
	  let hies_elt = dexp3_list_tr d3es_elt in
	    hiexp_arr loc0 hit0 hit_elt hies_elt
      | DE3assgn_ptr (d3e_ptr, d3ls, d3e_val) ->
	  if dexp3_is_proof d3e_val then hiexp_empty loc0 hit0
	  else begin
	    let hie_ptr = dexp3_tr d3e_ptr in
	    let hils = dlab3_list_tr loc0 d3ls in
	    let hie_val = dexp3_tr d3e_val in
	      hiexp_assgn_ptr loc0 hit0 hie_ptr hils hie_val
	  end
      | DE3assgn_var (d2v, d3ls, d3e_val) ->
	  if dexp3_is_proof d3e_val then hiexp_empty loc0 hit0
	  else begin
	    let () = dvar2_ntimes_inc d2v in
	    let hils = dlab3_list_tr loc0 d3ls in
	    let hie_val = dexp3_tr d3e_val in
	      hiexp_assgn_var loc0 hit0 d2v hils hie_val
	  end
      | DE3case (sgn, d3es, c3ls) ->
	  let hies = List.map dexp3_tr d3es in
(*
	  let () =
	    P.fprintf stdout "dexp3_tr: DE2case: c3ls = %a\n"
	      fprint_cla3_list c3ls in
*)
	  let hicls = cla3_list_tr c3ls in
	    hiexp_case_if loc0 hit0 (sgn > 0) hies hicls
      | DE3char c -> hiexp_char loc0 hit0 c
      | DE3con (d2c, (npf, d3es_arg)) ->
(*
	  let () =
	    P.fprintf stdout "dexp3_tr: d2c = %a\n" fprint_dcon2 d2c in
	  let () =
	    P.fprintf stdout "dexp3_tr: npf = %i\n" npf in
	  let () =
	    P.fprintf stdout
	      "dexp3_tr: d3es_arg = %a\n" fprint_dexp3_list d3es_arg in
*)
	  let hies_arg = dexp3_arg_list_tr npf d3es_arg in
(*
	  let () = 
	    P.fprintf stdout
	      "dexp3_tr: hies_arg = %a\n" fprint_hiexp_list hies_arg in
*)
	  let hits_arg = List.map (function hie -> hie.hiexp_type) hies_arg in
	  let hit_sum = hityp_sum_tmp d2c hits_arg in
	    hiexp_con loc0 hit0 hit_sum d2c hies_arg
      | DE3cst d2c -> (* d2c is external as it is used *)
	  dexp3_cst_tr loc0 hit0 d2c
      | DE3crypt (_(*knd*), d3e) -> dexp3_tr d3e
      | DE3delay (lin, d3e) ->
	  let hie = dexp3_tr d3e in hiexp_delay loc0 hit0 lin hie
      | DE3dynload f -> hiexp_dynload loc0 hit0 f
      | DE3empty -> hiexp_empty loc0 hit0
      | DE3extval code -> hiexp_extval loc0 hit0 code
      | DE3fix (d2v, d3e) ->
	  let hie = dexp3_tr d3e in
	  let () =
	    if not (hiexp_is_value hie) then begin
	      P.fprintf stderr "%a: non-value fixed-point dynamic expression.\n"
		Loc.fprint loc0;
	      Err.abort ();
	    end in
	    hiexp_fix loc0 hit0 d2v hie
      | DE3float f -> hiexp_float loc0 hit0 f
      | DE3foldat _ -> hiexp_empty loc0 hit0
      | DE3freeat d3e ->
	  let hie = dexp3_tr d3e in hiexp_freeat loc0 hit0 hie
      | DE3if (d3e_cond, d3e_then, d3e_else) ->
	  let hie_cond = dexp3_tr d3e_cond in
	  let hie_then = dexp3_tr d3e_then in
	  let hie_else = dexp3_tr d3e_else in
	    hiexp_if loc0 hit0 hie_cond hie_then hie_else
      | DE3int (ik, i) -> hiexp_int loc0 hit0 ik i
      | DE3lam_dyn (is_lin, (npf, p3ts_arg), d3e_body) ->
	  let hit_fun = sexp2_tr_1 d3e0.dexp3_type in
	  let hips_arg = pat3_arg_list_tr npf p3ts_arg in
	  let hie_body = dexp3_tr d3e_body in 
	    hiexp_lam loc0 hit_fun hips_arg hie_body
      | DE3lam_sta (s2vs, s2ps, d3e) ->
	  let hie = dexp3_tr d3e in
	  let () =
	    if not (hiexp_is_value hie) then begin
	      P.fprintf stderr "%a: non-value static lambda-abstration.\n"
		Loc.fprint loc0;
	      Err.abort ();
	    end in hie
      | DE3let (d3cs, d3e) ->
	  let hids = dec3_list_tr d3cs in
	  let hie = dexp3_tr d3e in
	    hiexp_let_simplify loc0 hit0 hids hie
      | DE3loopexn i -> hiexp_loopexn loc0 hit0 i
      | DE3lst d3es ->
	  let hies = dexp3_list_tr d3es in hiexp_lst loc0 hit0 hies
      | DE3ptrof_ptr (d3e, d3ls) ->
	  let hie = dexp3_tr d3e in
	  let hils = dlab3_list_tr loc0 d3ls in
	    hiexp_ptrof_ptr loc0 hit0 hie hils
      | DE3ptrof_var (d2v, d3ls) ->
	  let () = dvar2_ntimes_inc d2v in
	  let hils = dlab3_list_tr loc0 d3ls in
	    hiexp_ptrof_var loc0 hit0 d2v hils
      | DE3raise d3e_exn ->
	  let hie_exn = dexp3_tr d3e_exn in
	    hiexp_raise loc0 hit0 hie_exn
      | DE3rec (is_flat, (npf, ld3es)) ->
	  let hit_rec = sexp2_tr_1 d3e0.dexp3_type in
	  let lhies = labdexp3_arg_list_tr npf ld3es in
	    hiexp_rec loc0 hit0 is_flat hit_rec lhies
      | DE3refarg (refval, freeknd, d3e) ->
	  let hie = dexp3_tr d3e in
	    hiexp_refarg loc0 hit0 refval freeknd hie
      | DE3sel (d3e, d3ls) ->
	  let hie = dexp3_tr d3e in
	  let hils = dlab3_list_tr loc0 d3ls in
	    hiexp_sel loc0 hit0 hie hils
      | DE3sel_ptr (d3e_ptr, d3ls) ->
	  let hie_ptr = dexp3_tr d3e_ptr in
	  let hils = dlab3_list_tr loc0 d3ls in
	    hiexp_sel_ptr loc0 hit0 hie_ptr hils
      | DE3sel_var (d2v, d3ls) ->
	  let () = dvar2_ntimes_inc d2v in
	  let hils = dlab3_list_tr loc0 d3ls in
	    hiexp_sel_var loc0 hit0 d2v hils
      | DE3seq d3es -> dexp3_seq_tr loc0 hit0 d3es
      | DE3string s -> hiexp_string loc0 hit0 s
      | DE3struct ld3es ->
	  let hit_rec = sexp2_tr_1 d3e0.dexp3_type in
	  let lhies = labdexp3_arg_list_tr 0 ld3es in
	    hiexp_rec loc0 hit0 true (* is_flat *) hit_rec lhies
      | DE3template_cst (d2c, s2ess) ->
	  let hit_fun = sexp2_tr_1 d3e0.dexp3_type in
	    dexp3_template_cst_tr loc0 hit_fun d2c s2ess
      | DE3template_var (d2v, s2ess) ->
	  let hit_fun = sexp2_tr_1 d3e0.dexp3_type in
	    dexp3_template_var_tr loc0 hit_fun d2v s2ess
      | DE3top -> hiexp_top loc0 hit0
      | DE3trywith (d3e, c3ls) ->
	  let hie = dexp3_tr d3e in
	  let hicls = cla3_list_tr c3ls in
	    hiexp_trywith loc0 hit0 hie hicls
      | DE3var d2v -> begin
	  if dvar2_is_not_proof d2v then
	    let () = dvar2_ntimes_inc d2v in hiexp_var loc0 hit0 d2v
	  else begin
	    P.eprintf
	      "%a: dexp3_tr: the proof variable <%a> needs to be erased!\n"
	      Loc.fprint loc0 fprint_dvar2 d2v;
	    Err.abort ();
	  end
	end
      | DE3viewat_assgn_ptr _ -> hiexp_empty loc0 hit0
      | DE3viewat_assgn_var _ -> hiexp_empty loc0 hit0
      | DE3while (d3e_test, d3e_body) ->
	  let hie_test = dexp3_tr d3e_test in
	  let hie_body = dexp3_tr d3e_body in
	    hiexp_while loc0 hit0 hie_test hie_body
      | _ -> begin
	  P.fprintf stderr "dexp3_tr: d3e0 = %a\n" fprint_dexp3 d3e0;
	  Err.abort ();
	end
(* end of [dexp3_tr] *)

(* ****** ****** *)

and dexp3_opt_tr (od3e: dexp3 option): hiexp option =
  match od3e with Some d3e -> Some (dexp3_tr d3e) | None -> None

and dexp3_list_tr (d3es: dexp3 list): hiexp list =
  List.map dexp3_tr d3es

and dexp3_arg_list_tr (npf: int) (d3es: dexp3 list): hiexp list =
  let rec aux i = function
    | d3e :: d3es ->
	if i < npf then aux (i+1) d3es
	else if d3e.dexp3_is_proof then aux (i+1) d3es
	else (dexp3_tr d3e) :: aux (i+1) d3es
    | [] -> [] in
    aux 0 d3es
(* end of [dexp3_arg_list_tr] *)

and labdexp3_arg_list_tr (npf: int) (ld3es: labdexp3 list): labhiexp list =
  let rec aux i ld3es = match ld3es with
    | (l, d3e) :: ld3es ->
	if i < npf then aux (i+1) ld3es
	else if d3e.dexp3_is_proof then aux (i+1) ld3es
	else (l, dexp3_tr d3e) :: aux (i+1) ld3es
    | [] -> [] in
    aux 0 ld3es
(* end of [labdexp3_arg_list_tr] *)

(* ****** ****** *)

and dexp3_fun_arg_list_tr
  (is_vararg: bool) (npf: int) (d3es: dexp3 list): hiexp list =
  let rec aux0 hies = function
    | (l, d3e) :: ld3es ->
	let hie = dexp3_tr d3e in aux0 (hie :: hies) ld3es
    | [] -> List.rev hies in
  let rec aux1 hies d3e = function
    | d3e1 :: d3es1 ->
	let hie = dexp3_tr d3e in aux1 (hie :: hies) d3e1 d3es1
    | [] -> begin
	if is_vararg then begin match d3e.dexp3_node with
	  | DE3rec (_, (_, ld3es)) -> aux0 hies ld3es
	  | _ -> error_of_deadcode "ats_trans4: dexp3_fun_arg_list_tr"
	end else List.rev (dexp3_tr d3e :: hies)
      end in
  let rec aux2 i = function
    | d3e :: d3es ->
	if i < npf then aux2 (i+1) d3es else aux1 [] d3e d3es
    | [] -> [] in
    aux2 0 d3es
(* end of [dexp3_fun_arg_list_tr] *)

(* ****** ****** *)

and dexp3_seq_tr loc (hit0: hityp) (d3es: dexp3 list): hiexp =
  let hies = List.map dexp3_tr d3es in hiexp_seq_simplify loc hit0 hies

(* ****** ****** *)

and dexp3_cst_tr loc0 (hit0: hityp) (d2c: dcst2): hiexp =
  match d2c with
    | _ when dcst2_is_bool_true d2c -> hiexp_bool loc0 hit0 true
    | _ when dcst2_is_bool_false d2c -> hiexp_bool loc0 hit0 false
    | _ -> hiexp_cst loc0 hit0 d2c
(* end of [dexp3_cst_tr] *)

and dexp3_template_cst_tr loc0
  (hit0: hityp) (d2c: dcst2) (s2ess: sexp2 list list): hiexp =
  match d2c with
    | _ when dcst2_is_sizeof d2c -> begin match s2ess with
	| [[s2e_arg]] -> hiexp_sizeof loc0 hit0 (sexp2_tr_0 s2e_arg)
	| _ -> begin
	    error_of_deadcode "ats_trans4: dexp3_template_cst_tr"
	  end
      end
    | _ -> begin
	let hitss = List.map (List.map sexp2_tr_0) s2ess in
(*
	let () =
	  P.fprintf stdout "dexp3:template_cst_tr: hitss = %a\n"
	    fprint_hityp_list_list hitss in
*)
	  hiexp_template_cst loc0 hit0 d2c hitss
      end
(* end of [dexp3_template_cst_tr] *)

and dexp3_template_var_tr loc0
  (hit0: hityp) (d2v: dvar2) (s2ess: sexp2 list list): hiexp =
  let hitss = List.map (List.map sexp2_tr_0) s2ess in
    hiexp_template_var loc0 hit0 d2v hitss

(* ****** ****** *)

and dlab3_list_tr loc0 (d3ls: dlab3 list): hilab list =
  let rec aux d3ls = match d3ls with
    | d3l :: d3ls -> begin
	match d3l.dlab3_lab, d3l.dlab3_ind with
	  | Some (l, s2e_rec), Some (d3ess, s2e_elt) ->
	      let hit_rec = sexp2_tr_1 s2e_rec in
	      let hit_elt = sexp2_tr_0 s2e_elt in
	      let hiess = List.map dexp3_list_tr d3ess in
	      let hil1 = hilab_lab loc0 l hit_rec in
	      let hil2 = hilab_ind loc0 hit_elt hiess in
		 hil1 :: hil2 :: aux d3ls
	  | Some (l, s2e_rec), None ->
	      let hit_rec = sexp2_tr_1 s2e_rec in
	      let hil = hilab_lab loc0 l hit_rec in
		hil :: aux d3ls
	  | None, Some (d3ess, s2e_elt) ->
	      let hit_elt = sexp2_tr_0 s2e_elt in
	      let hiess = List.map dexp3_list_tr d3ess in
	      let hil = hilab_ind loc0 hit_elt hiess in
		hil :: aux d3ls
	  | None, None -> aux d3ls
      end
    | [] -> [] in
    aux d3ls
(* end of [dlab3_list_tr] *)

(* ****** ****** *)

and cla3_tr (c3l: cla3): hicla =
  let loc = c3l.cla3_loc in
(*
  let () =
    P.fprintf stdout "cla3_tr: c3l = %a\n" fprint_cla3 c3l in
*)
  let hips = pat3_list_tr c3l.cla3_pat in
(*
  let () =
    P.fprintf stdout "cla3_tr: hips = %a\n" fprint_hipat_list hips in
*)
  let gua = dexp3_opt_tr c3l.cla3_gua in
  let body = dexp3_tr c3l.cla3_body in
    hicla loc hips gua body
(* end of [cla3_tr] *)

and cla3_list_tr (c3ls: cla3 list): hicla list =
  let rec aux = function
    | c3l :: c3ls -> begin
	if c3l.cla3_isneg then aux c3ls else
	  let hicl = cla3_tr c3l and hicls = aux c3ls in hicl :: hicls
      end
    | [] -> [] in
    aux c3ls
(* end of [cla3_list_tr] *)

(* ****** ****** *)

and dec3_fun_tr (istemp: bool) (d: dec3_fun): hidec_fun =
  let loc = d.dec3_fun_loc in
  let d2v_fun = d.dec3_fun_name in
  let hie_def = dexp3_tr d.dec3_fun_def in
  let () = if istemp then
    tempdef_var_map_add d2v_fun hie_def in
(*
  let () = P.fprintf stdout "dec3_fun_tr: d2v_fun = %a\n" fprint_dvar2 d2v_fun in
  let () = P.fprintf stdout "dec3_fun_tr: hie_def = %a\n" fprint_hiexp hie_def in
*)
    hidec_fun loc d2v_fun hie_def
(* end of [dec3_fun_tr] *)

and dec3_fun_list_tr
  (istemp: bool) (ds: dec3_fun list): hidec_fun list =
  List.map (dec3_fun_tr istemp) ds

(* ****** ****** *)

and dec3_val_tr (d: dec3_val): hidec_val =
  let loc = d.dec3_val_loc in
  let hip = pat3_tr d.dec3_val_pat in
  let hie = dexp3_tr d.dec3_val_def in
    hidec_val loc hip hie
(* end of [dec3_val_tr] *)

and dec3_val_list_tr (ds: dec3_val list): hidec_val list =
  List.map dec3_val_tr ds

(* ****** ****** *)

and dec3_var_tr (d: dec3_var): hidec_var =
  let loc = d.dec3_var_loc in
  let d2v_ptr = d.dec3_var_ptr in
  let ohie_ini = match d.dec3_var_ini with
    | Some d3e -> Some (dexp3_tr d3e) | None -> None in
    hidec_var loc d2v_ptr ohie_ini
(* end of [dec3_var_tr] *)

and dec3_var_list_tr (ds: dec3_var list): hidec_var list =
  List.map dec3_var_tr ds

(* ****** ****** *)

and dec3_impl_list_tr (ds: dec3_impl list): hidec_impl list =
  let rec aux hids ds = match ds with
    | d :: ds -> begin
	let d2c = d.dec3_impl_cst in
	let hids =
	  if dcst2_is_proof d2c then hids
	  else begin
	    let decarg = d.dec3_impl_decarg in
	    let istemp = match decarg with _ :: _ -> true | [] -> false in
	    let def = dexp3_tr d.dec3_impl_def in
	    let () = if istemp then tempdef_cst_tbl_add d2c decarg def in
	    let hid = hidec_impl d.dec3_impl_loc d2c istemp decarg def in
	      hid :: hids
	  end in
	  aux hids ds
      end
    | [] -> List.rev hids in
    aux [] ds
(* end of [dec3_impl_list_tr] *)

(* ****** ****** *)

and dec3_list_tr_aux1 (ds: dec3 list) (res: hidec list): hidec list =
  match ds with
    | d :: ds -> dec3_list_tr_aux2 d ds res
    | [] -> List.rev res

and dec3_list_tr_aux2
  (d: dec3) (ds: dec3 list) (res: hidec list): hidec list =
  match d.dec3_node with
    | DC3extype (name, s2e_def) ->
	let hit_def = sexp2_tr_1 s2e_def in
	let hid = hidec_extype d.dec3_loc name hit_def in
	  dec3_list_tr_aux1 ds (hid :: res)

    | DC3extval (name, d3e_def) ->
	let hie_def = dexp3_tr d3e_def in
	let hid = hidec_extval d.dec3_loc name hie_def in
	  dec3_list_tr_aux1 ds (hid :: res)

    | DC3dyncsts (dck, d2cs) ->
	let hid = hidec_dyncsts d.dec3_loc dck d2cs in
	  dec3_list_tr_aux1 ds (hid :: res)

    | DC3data (dtk, s2cs) ->
	let hid = hidec_data d.dec3_loc dtk s2cs in
	  dec3_list_tr_aux1 ds (hid :: res)

    | DC3exns d2cs ->
        let () = List.iter exn_con_set_add d2cs in
	  dec3_list_tr_aux1 ds res

    | DC3impls xs -> begin
	let xs = dec3_impl_list_tr xs in
	let hid = hidec_impls d.dec3_loc xs in
	  dec3_list_tr_aux1 ds (hid :: res)
      end

    | DC3funs (istemp, fk, xs) -> begin
	let res =
	  if Syn.funkind_is_proof fk then res else begin
	    let xs = dec3_fun_list_tr istemp xs in
	    let hid = hidec_funs d.dec3_loc istemp fk xs in
	      hid :: res
	  end in
	  dec3_list_tr_aux1 ds res
      end

    | DC3vals (vk, xs) -> begin
	let res =
	  if Syn.valkind_is_proof vk then res
	  else begin
	    let xs = dec3_val_list_tr xs in
	    let d = hidec_vals d.dec3_loc vk xs in
	      d :: res
	  end in
	  dec3_list_tr_aux1 ds res
      end

    | DC3valpars xs ->
	let xs = dec3_val_list_tr xs in
	let d = hidec_valpars d.dec3_loc xs in
	  dec3_list_tr_aux1 ds (d :: res)

    | DC3valrecs xs ->
	let xs = dec3_val_list_tr xs in
	let d = hidec_valrecs d.dec3_loc xs in
	  dec3_list_tr_aux1 ds (d :: res)

    | DC3vars (is_stack, xs) -> begin
	let xs = dec3_var_list_tr xs in
	let hid = hidec_vars d.dec3_loc is_stack xs in
	  dec3_list_tr_aux1 ds (hid :: res)
      end

    | DC3local (ds_head, ds_body) -> begin
	let hids_head = dec3_list_tr ds_head in
	let hids_body = dec3_list_tr ds_body in
	let hid = hidec_local d.dec3_loc hids_head hids_body in
	  dec3_list_tr_aux1 ds (hid :: res)
      end

    | DC3staload (f, ods) -> begin
	let ohids = match ods with
	  | None -> None | Some ds -> Some (dec3_list_tr ds) in
	let hid = hidec_staload d.dec3_loc f ohids in
	  dec3_list_tr_aux1 ds (hid :: res)
      end

    | DC3dynload f -> begin
	let hid = hidec_dynload d.dec3_loc f in
	  dec3_list_tr_aux1 ds (hid :: res)
      end

    | DC3extern (pos, code) -> begin
	let hid = hidec_extern d.dec3_loc pos code in
	  dec3_list_tr_aux1 ds (hid :: res)
      end

and dec3_list_tr (ds: dec3 list): hidec list = dec3_list_tr_aux1 ds []

(* ****** ****** *)

let initialize (filename: Fil.filename): unit =
  let base = Fil.filename_fullname_id filename in begin
      typedef_base_set base;
      typedef_list_reset ();
      typedef_map_reset ();
      (* tagging exception constructors *)
      the_exn_con_set := DconSet.empty;
      (* compiling templates *)
      tempdef_cst_tbl_clear ();
      tempdef_var_map_reset ();
  end (* end of [initialize] *)

(* ****** ****** *)

(* end of [ats_trans4.ml] *)
