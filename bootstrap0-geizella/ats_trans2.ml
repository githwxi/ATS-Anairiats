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

module PR = Printf

module Err = Ats_error
module Eff = Ats_effect
module Fil = Ats_filename
module Lab = Ats_label
module Loc = Ats_location
module NS = Ats_name_space
module Sym = Ats_symbol
module Syn = Ats_syntax

module Env1 = Ats_env1
module SEnv2 = Ats_staenv2
module SDEnv2 = Ats_stadynenv2

open Ats_staexp1
open Ats_dynexp1
open Ats_staexp2
open Ats_staexp2_util
open Ats_stacst2
open Ats_dynexp2
open Ats_dynexp2_util
open Ats_dyncst2
open Ats_errmsg2

open Ats_misc

(* ****** ****** *)

type lab = Lab.label
type loc = Loc.location
type symbol = Sym.symbol

(* two standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_trans2: "; Err.error s;
end

let error_with_loc (loc: loc) (s: string): 'a = begin
  prerr_string "ats_trans2: "; Err.error_with_loc loc s;
end

(* ****** ****** *)

(* combinations of pushs, pops and merges *)

let get_top_all ()
  : SEnv2.SRT2env.table * SEnv2.SEXP2env.table * SDEnv2.DEXP2env.table =
  (SEnv2.SRT2env.get_top (),
   SEnv2.SEXP2env.get_top (),
   SDEnv2.DEXP2env.get_top ())

let save_all (): unit = begin
  Env1.E0xpEnv.save ();
  SEnv2.SRT2env.save ();
  SEnv2.SEXP2env.save ();
  SDEnv2.DEXP2env.save ();
  NS.NameSpace.save ();
end

let restore_all (): unit = begin
  Env1.E0xpEnv.restore ();
  SEnv2.SRT2env.restore ();
  SEnv2.SEXP2env.restore ();
  SDEnv2.DEXP2env.restore ();
  NS.NameSpace.restore ();
end

let push_all (): unit = begin
  SEnv2.SRT2env.push ();
  SEnv2.SEXP2env.push ();
  SDEnv2.DEXP2env.push ();
  NS.NameSpace.push ();
end

let pop_all (): unit = begin
  SEnv2.SRT2env.pop ();
  SEnv2.SEXP2env.pop ();
  SDEnv2.DEXP2env.pop ();
  NS.NameSpace.pop ();
end

let localjoin_all (): unit = begin
  SEnv2.SRT2env.localjoin ();
  SEnv2.SEXP2env.localjoin ();
  SDEnv2.DEXP2env.localjoin ();
  NS.NameSpace.localjoin ();
end

(* ****** ****** *)

(* functions for finding declared symbols *)

let srt2_env_find_sym (id: symbol): srtext2 option =
  match SEnv2.SRT2env.find id with
    | None -> NS.srt2_env_find id
    | ans -> ans

let srt2_env_find_id (id: Syn.srt_id): srtext2 option =
  srt2_env_find_sym (Syn.sym_of_srt_id id)

let sexp2_env_find_sym (id: symbol): sitem2 option =
  match SEnv2.SEXP2env.find id with
    | None -> NS.sexp2_env_find id
    | ans -> ans

let sexp2_env_find_id (id: Syn.sid): sitem2 option =
  sexp2_env_find_sym (Syn.sym_of_sid id)

let sexp2_env_file_find_sym (f: Fil.filename) (id: symbol): sitem2 option =
  let name = NS.make_name (Fil.filename_fullname f) in
    match NS.stadynenv_find name with
      | Some (_, t, _, _) -> SEnv2.SEXP2env.table_find id t
      | None -> None

let sexp2_env_file_find (f: Fil.filename) (id: Syn.sid): sitem2 option =
  sexp2_env_file_find_sym f (Syn.sym_of_sid id)

let sexp2_env_sym_find (s: symbol) (id: Syn.sid): sitem2 option =
  match srt2_env_find_sym s with
    | Some s2te -> begin
	match s2te with
	  | STE2srt (SRT2bas (SRT2BASdef sd2t)) ->
	      let s2cs =
		List.filter
		  (function s2c -> Syn.sid_eq id s2c.scst2_name)
		  sd2t.srt2_dat_con in
		Some (SI2cst s2cs)
	  | _ -> None
      end (* end of [Some] *)
    | None -> begin
	match sexp2_env_find_sym s with
	  | Some (SI2fil f) -> sexp2_env_file_find f id
	  | _ -> None
      end (* end of [None] *)

let sexp2_env_qfind
  (sq: Syn.squal) (id: Syn.sid): sitem2 option =
  match sq with
    | Syn.SQ_filedot f -> sexp2_env_file_find f id
    | Syn.SQ_symcolon s -> sexp2_env_sym_find s id
    | Syn.SQ_symdot s -> begin
	match sexp2_env_find_sym (Sym.staload_symbol s) with
	  | Some (SI2fil f) -> sexp2_env_file_find f id
	  | _ -> None
      end
(* end of [sexp2_env_qfind] *)

let sexp2_env_oqfind ((osq, id): Syn.squal_opt_id): sitem2 option =
  match osq with
    | Some f -> sexp2_env_qfind f id | None -> sexp2_env_find_id id
(* end of [sexp2_env_oqfind] *)

(* ****** ****** *)

let sexp2_env_add_cst (s2c: scst2): unit = begin
  let id = s2c.scst2_name in match sexp2_env_find_id id with
    | Some (SI2cst s2cs) -> SEnv2.sexp2_env_add_cst_list id (s2c :: s2cs)
    | _ -> SEnv2.sexp2_env_add_cst_list id [s2c]
end (* end of [sexp2_env_add_cst] *)

(* ****** ****** *)

let dcon2_scst2_find (s2c: scst2) (id: Syn.did): ditem2 option =
  match s2c.scst2_cons with
    | Some d2cs -> begin
	let d2cs = List.filter
          (function d2c -> Syn.did_eq id d2c.dcon2_name) d2cs in
	  Some (DI2con d2cs)
      end (* end of [Some] *)
    | None -> None
(* end of [dcon2_scst2_find] *)

let dexp2_env_find_sym
  (id: symbol): ditem2 option = begin
  match SDEnv2.DEXP2env.find id with
    | None -> NS.dexp2_env_find id | ans -> ans
end (* end of [dexp2_env_find_sym] *)

let dexp2_env_find (id: Syn.did): ditem2 option =
  dexp2_env_find_sym (Syn.sym_of_did id)

let dexp2_env_file_find_sym
  (f: Fil.filename) (id: symbol): ditem2 option = begin
  let name = NS.make_name (Fil.filename_fullname f) in
    match NS.stadynenv_find name with
      | Some (_, _, t, _) -> SDEnv2.DEXP2env.table_find id t
      | None -> None
end (* end of [dexp2_env_file_find_sym] *)

let dexp2_env_file_find
  (f: Fil.filename) (id: Syn.did): ditem2 option =
  dexp2_env_file_find_sym f (Syn.sym_of_did id)

let dexp2_env_file_sym_find
  (f: Fil.filename) (s: Syn.sid) (id: Syn.did): ditem2 option =
  match sexp2_env_file_find f s with
    | Some (SI2cst [s2c]) -> dcon2_scst2_find s2c id
    | _ -> None
(* end of [dexp2_end_file_sym_find] *)

let dexp2_env_qfind
  (q: Syn.dqual) (id: Syn.did): ditem2 option = begin
  match q with
    | Syn.DQ_filedot f -> dexp2_env_file_find f id
    | Syn.DQ_filedot_symcolon (f, s) -> dexp2_env_file_sym_find f s id
    | Syn.DQ_symcolon s -> begin
	match sexp2_env_find_sym s with
	  | Some (SI2cst [s2c]) -> dcon2_scst2_find s2c id
	  | _ -> None
      end
    | Syn.DQ_symdot s -> begin
	match sexp2_env_find_sym (Sym.staload_symbol s) with
	  | Some (SI2fil f) -> dexp2_env_file_find f id
	  | _ -> None
      end
    | Syn.DQ_symdot_symcolon (s1, s2) -> begin
	match sexp2_env_find_sym (Sym.staload_symbol s1) with
	  | Some (SI2fil f) -> dexp2_env_file_sym_find f s2 id
	  | _ -> None
      end
end (* end of [dexp2_env_qfind] *)

let dexp2_env_oqfind ((odq, id): Syn.dqual_opt_id): ditem2 option =
  match odq with
    | Some f -> dexp2_env_qfind f id | None -> dexp2_env_find id

(* ****** ****** *)

let rec srt1_tr (s1t: srt1): srt2 = begin
  match s1t.srt1_node with
  | SRT1app (s1t, s1ts) -> srt1_app_tr s1t.srt1_loc s1t s1ts
  | SRT1id id -> begin match srt2_env_find_id id with
      | Some (STE2srt s2t) -> s2t
      | Some (STE2sub _) -> srt1_tr_errmsg_id_subset s1t id
      | None -> srt1_tr_errmsg_id_undef s1t id
    end
  | SRT1lam (arg, res) -> begin
      let arg = List.map srt2_var_make arg in
      let () = SEnv2.SRT2env.push () in
      let () = SEnv2.srt2_env_add_var_list arg in
      let res = srt1_tr res in
      let () = SEnv2.SRT2env.pop () in
	srt2_lam arg res
    end
  | SRT1tup s1ts -> SRT2tup (srt1_list_tr s1ts)
  | SRT1list _ -> srt1_tr_errmsg_list (s1t)
  | SRT1qid _ -> srt1_tr_errmsg_qid (s1t)
end (* end of [srt1_tr] *)

and srt1_list_tr (s1ts: srt1 list): srt2 list = List.map srt1_tr s1ts
and srt1_opt_tr (os1t: srt1 option): srt2 option =
  match os1t with None -> None | Some s1t -> Some (srt1_tr s1t)

and srt1_app_tr (loc: loc) (s1t: srt1) (s1ts: srt1 list): srt2 =
  if srt1_is_arrow s1t then begin match s1ts with
    | [s1t1; s1t2] ->
        let s2t2 = srt1_tr s1t2 in begin
	  match s1t1.srt1_node with
	    | SRT1list s1ts1 -> srt2_fun (srt1_list_tr s1ts1) s2t2
	    | _ -> srt2_fun [srt1_tr s1t1] s2t2
        end (* end of [let] *)
    | _ -> error_with_loc loc ("srt1_app_tr: impossible")
  end else begin
    srt2_app (srt1_tr s1t) (srt1_list_tr s1ts)
  end (* end of [if] *)
(* end of [srt1_app_tr] *)

(* ****** ****** *)

let effvar_tr loc0 (effv: Eff.effvar): sexp2 = begin
  match sexp2_env_find_id effv with
    | Some (SI2var s2v) -> sexp2_var (s2v) | _ -> begin 
	PR.fprintf stderr
	  "%a: effvar_tr: unrecognized static identifier: <%a>\n"
	  Loc.fprint loc0 Eff.fprint_effvar effv;
	Err.abort ();
      end (* end of [_] *)
end (* end of [effvar_tr] *)

let effvars_tr loc0 (effvs: Eff.effvars): sexp2 list =
  List.map (effvar_tr loc0) effvs

let effcst_tr loc0 (effc: Eff.effcst): seff2 = begin match effc with
    | Eff.EFFCall -> SEFF2all
    | Eff.EFFCnil -> SEFF2nil
    | Eff.EFFCset (effs, effvs) -> SEFF2set (effs, effvars_tr loc0 effvs)
end (* end of [effcst_tr] *)

(* ****** ****** *)

let rec sexp1_app_unwind s1e s1ess = begin
  match s1e.sexp1_node with
    | SE1app (s1e, s1es) -> sexp1_app_unwind s1e (s1es :: s1ess)
    | SE1qid (osq, id) -> begin match osq with
	| Some _ -> (s1e, s1ess)
	| None -> begin
	    match Env1.e0xp1_find_sym (Syn.sym_of_sid id) with
	      | Some e ->
		  let s1e = sexp1_of_e0xp1 s1e.sexp1_loc e in
		    sexp1_app_unwind s1e s1ess
	      | None -> (s1e, s1ess)
	  end
      end
    | _ -> (s1e, s1ess)
end (* end of [sexp1_app_unwind] *)

let rec sexp1_tr_up (s1e0: sexp1): sexp2 =
  let loc0 = s1e0.sexp1_loc in match s1e0.sexp1_node with
    | SE1ann (s1e, s1t) -> let s2t = srt1_tr s1t in sexp1_tr_dn s1e s2t
(*
    | SE1any -> error_with_loc s1e.sexp1_loc "sexp1_tr: SE1any"
*)
    | SE1app (s1e, s1es) -> begin
	let (s1e_opr, s1ess_arg) = sexp1_app_unwind s1e [s1es] in
	  match s1e_opr.sexp1_node with
	    | SE1qid qid -> begin match specsid_of_squal_opt_id qid with
		| SSarrow -> begin
		    sexp1_arrow_tr_up loc0 None 0(*lin*) 0(*prf*) None s1ess_arg
		  end
		| SSnone -> begin match sexp2_env_oqfind qid with
		    | Some s2i -> sexp1_app_id_tr_up
			loc0 (s1e_opr.sexp1_loc) qid s2i s1ess_arg
		    | None -> sexp1_tr_up_errmsg_appid_none s1e qid
		  end
	      end
	    | SE1imp (fc, lin, prf, oeffc) ->
		sexp1_arrow_tr_up loc0 (Some fc) lin prf oeffc [s1es]

	    | _ -> begin
		let s2e_opr = sexp1_tr_up s1e_opr in
		  sexp1_app_tr_up s1e.sexp1_loc s2e_opr s1ess_arg
	      end
      end

    | SE1char c -> sexp2_char c

    | SE1exi (squas1, s1e) ->
	let () = SEnv2.SEXP2env.push () in
	let (s2vs, s2es) = squas1_tr squas1 in
	let s2e = sexp1_tr_up s1e in
	let () = SEnv2.SEXP2env.pop () in
	  sexp2_exi s2vs s2es s2e

    | SE1int i -> sexp2_intinf i

    | SE1invar _ -> sexp1_tr_up_errmsg_invar s1e0

    | SE1lam (arg1, res1, body1) ->
	let aux (id, os1t) =
	  let s2v = match os1t with
	    | Some s1t -> svar2_new_with_id id (srt1_tr s1t)
	    | None -> sexp1_tr_up_errmsg_lam_nosrt s1e0 id in
	    (SEnv2.sexp2_env_add_var s2v; s2v) in
	let () = SEnv2.SEXP2env.push () in
	let s2vs = List.map aux arg1 in
	let body2 = match res1 with
	  | Some s1t -> let s2t = srt1_tr s1t in sexp1_tr_dn body1 s2t
	  | None -> sexp1_tr_up body1 in
	let () = SEnv2.SEXP2env.pop () in
	let s2ts = List.map (function s2v -> s2v.svar2_sort) s2vs in
	  sexp2_lam_with_sort (srt2_fun s2ts body2.sexp2_sort) s2vs body2

    | SE1list (npf, s1es) -> sexp1_tytup_tr_up true (* is_flat *) npf s1es

    | SE1mod (qid, ls1es) -> begin
        match sexp2_env_oqfind qid with
	  | Some s2i -> begin match s2i with
	      | SI2mod (ls2vs, s2e) ->
		  let f (l, _, s1e) = (l, sexp1_tr_dn_impredicative s1e) in
		  let ls2es = List.map f ls1es in sexp1_mod_tr loc0 ls2vs s2e ls2es
	      | _ -> sexp1_tr_up_errmsg_mod_unmod s1e0 qid
	    end
	  | None -> sexp1_tr_up_errmsg_mod_undef s1e0 qid
      end

    | SE1qid ((osq, id) as qid) -> begin match osq with
	| Some _ -> sexp1_id_tr_up loc0 qid
	| None -> begin
	    let s = Syn.sym_of_sid id in
	      match Env1.e0xp1_find_sym s with
		| Some e -> sexp1_tr_up (sexp1_of_e0xp1 loc0 e)
		| None -> sexp1_id_tr_up loc0 qid
	    end
      end

    | SE1struct ls1es -> sexp1_struct_tr_up ls1es

    | SE1top (s2e_opr, s2es_arg) -> sexp1_qmark_tr_up loc0 s2e_opr s2es_arg

    | SE1trans _ -> sexp1_tr_up_errmsg_trans s1e0

    | SE1tyarr (s1e_elt, s1ess_dim) ->
	let s2e_elt = sexp1_tr_dn_viewt0ype s1e_elt in
	let s2ess_dim = List.map (List.map sexp1_tr_dn_int) s1ess_dim in
	  sexp2_tyarr s2e_elt s2ess_dim

    | SE1tyrec (is_flat, ls1es) -> sexp1_tyrec_tr_up is_flat ls1es 

    | SE1tytup (is_flat, (npf, s1es)) -> sexp1_tytup_tr_up is_flat npf s1es 

    | SE1uni (squas1, s1e) ->
	let () = SEnv2.SEXP2env.push () in
	let (s2vs, s2es) = squas1_tr squas1 in
	let s2e = sexp1_tr_up s1e in
	let () = SEnv2.SEXP2env.pop () in
	  sexp2_uni s2vs s2es s2e

    | SE1union (s1e, ls1es) -> sexp1_union_tr_up s1e ls1es

    | _ -> begin
	PR.fprintf stderr "%a: sexp1_tr_up: unavailable: %a"
	  Loc.fprint loc0 fprint_sexp1 s1e0;
	Err.abort ()
      end
(* end of [sexp1_tr_up] *)

and sexp1_app_tr_up (loc: loc) (s2e: sexp2) (s1ess: (sexp1 list) list): sexp2 =
  let rec aux s2e = function
    | s1es :: s1ess ->
	let (s2ts, s2t) = match un_srt2_fun (s2e.sexp2_sort) with
	  | Some (s2ts, s2t) -> (s2ts, s2t)
	  | None -> sexp1_app_tr_up_errmsg_1 loc in
	let () =
	  let n1 = List.length s1es in
	  let n2 = List.length s2ts in
	    if n1 > n2 then sexp1_app_tr_up_errmsg_2 loc
	    else if n1 < n2 then sexp1_app_tr_up_errmsg_3 loc
	    else () in
	let s2es = sexp1_list_tr_dn loc s1es s2ts in
	  aux (sexp2_app_with_sort s2t s2e s2es) s1ess
    | [] -> s2e in
    aux s2e s1ess
(* end of [sexp1_app_tr_up] *)

and sexp1_app_id_tr_up (loc_app: loc) (loc_id: loc)
  (qid: Syn.squal_opt_id) (s2i: sitem2) (s1ess: (sexp1 list) list): sexp2 =
  match s2i with
    | SI2cst s2cs -> begin
	let s2ess = List.map sexp1_list_tr_up s1ess in
	let s2tss =
	  List.map (List.map (function s2e -> s2e.sexp2_sort)) s2ess in
(*
	let () =
	  PR.fprintf stdout "sexp1_app_id_tr_up: s2cs = %a\n"
	    fprint_scst2_with_sort_list s2cs in
	let () =
	  PR.fprintf stdout "sexp1_app_id_tr_up: s2tss = %a\n"
	    fprint_srt2_list_list s2tss in
*)
	  match scst2_select_with_argsorts s2cs s2tss with
	    | s2c :: _ -> sexp2_app_wind (sexp2_cst s2c) s2ess
	    | [] -> sexp1_app_id_tr_up_errmsg_none loc_id qid s2tss
      end
    | SI2datcon d2c -> sexp1_app_datcon_tr_up loc_app d2c s1ess
    | SI2var s2v -> sexp1_app_tr_up loc_app (sexp2_var s2v) s1ess
    | SI2fil _ -> sexp1_app_id_tr_up_errmsg_fil loc_id qid
    | SI2mod _ -> sexp1_app_id_tr_up_errmsg_mod loc_id qid
(* end of [sexp1_app_id_tr_up] *)

(* ****** ****** *)

and sexp1_app_datcon_tr_up (loc: loc)
  (d2c: dcon2) (s1ess: sexp1 list list): sexp2 = begin
  let s1es = match s1ess with
    | [] -> []
    | [s1es] -> s1es
    | _ -> sexp1_app_datcon_tr_errmsg_arg loc d2c in
  let s2es =
    List.map (function s1e -> sexp1_tr_dn s1e srt2_addr) s1es in
  let n = List.length s2es in
  let () = match compare n d2c.dcon2_arity_full with
    | 0 -> () | i -> sexp1_app_datcon_tr_errmsg_arity loc d2c i in
    sexp2_datcon d2c s2es
end (* end of [sexp1_app_datcon_tr_up] *)

(* ****** ****** *)

and sexp1_arg_tr_up (s1e0: sexp1): sexp2 = begin
  match s1e0.sexp1_node with
    | SE1invar (refval, s1e, s1es) -> begin
	sexp1_invar_tr_up s1e0.sexp1_loc refval s1e s1es
      end
    | SE1trans (s1e, s1es) -> begin
	sexp1_trans_tr_up s1e0.sexp1_loc s1e s1es
      end
    | _ -> sexp1_tr_up s1e0
end (* end of [sexp1_arg_tr_up] *)

and sexp1_arrow_tr_up loc0
  (ofc: Syn.funclo option) (lin: int) (prf: int)
  (oeffc: Eff.effcst option) (s1ess: sexp1 list list): sexp2 =
  let s1es = match s1ess with
    | [s1es] -> s1es | _ -> sexp1_arrow_tr_up_errmsg_app loc0 in
  let (s1e_arg, s1e_res) = match s1es with
    | [s1e1; s1e2] -> (s1e1, s1e2)
    | _ -> error_of_deadcode "ats_trans2: sexp1_arrow_tr_up" in
  let (npf, s1es_arg) = match s1e_arg.sexp1_node with
    | SE1list ns1es -> ns1es | _ -> (0, [s1e_arg]) in
  let s2es_arg =
    let rec aux_arg (s1es: sexp1 list): sexp2 list =
      match s1es with
	| s1e :: s1es -> begin
	    let s2e = sexp1_arg_tr_up s1e in
	    let s2t = s2e.sexp2_sort in
	      if srt2_is_impredicative s2t then begin
		if srt2_is_types s2t then begin match s1es with
		  | _ :: _ -> sexp1_arrow_tr_up_errmsg_vararg s1e
		  | _ -> [sexp2_vararg s2e]
		end else begin
		  s2e :: aux_arg s1es
		end
	      end else begin
		sexp1_arrow_tr_up_errmsg_arg s1e
	      end
	  end
	| [] -> [] in
      aux_arg s1es_arg in
  let s2e_res = sexp1_tr_dn_impredicative s1e_res in
  let s2t_res = s2e_res.sexp2_sort in
  let is_lin = lin > 0 in
  let is_prf = if prf > 0 then true else srt2_is_proof s2t_res in
  let fc = match ofc with
    | Some fc -> fc | None -> Syn.FUNCLOfun(*default*) in
  let s2t_fun = srt2_fun_lin_prf is_lin is_prf in
  let sf2e = match oeffc with
    | Some effc -> effcst_tr loc0 effc | None -> seff2_all in
    sexp2_funclo_with_sort s2t_fun fc lin sf2e (npf, s2es_arg) s2e_res
(* end of [sexp1_arrow_tr_up] *)

(* ****** ****** *)

and sexp1_invar_tr_up loc0
  (refval: int) (s1e_opr: sexp1) (s1es_arg: sexp1 list): sexp2 =
  let s1e = match s1es_arg with
    | [s1e] -> s1e | _ -> error_of_deadcode "sexp1_invar_tr_up" in
  let s2t = if refval = 0 then srt2_view else srt2_viewt0ype in
  let s2e = sexp1_tr_dn s1e s2t in
    sexp2_refarg refval s2e s2e
(* end of [sexp1_invar_tr_up] *)

(* ****** ****** *)

and sexp1_qmark_tr_up loc0
  (s1e_opr: sexp1) (s1es_arg: sexp1 list): sexp2 =
  let s1e = match s1es_arg with
    | [s1e] -> s1e | _ -> error_of_deadcode "sexp1_qmark_tr_up" in
  let s2e = sexp1_tr_dn_impredicative s1e in sexp2_top s2e
(* end of [sexp1_qmark_tr_up] *)

(* ****** ****** *)

and sexp1_trans_tr_up loc0
  (s1e_opr: sexp1) (s1es_arg: sexp1 list): sexp2 =
  let (s1e1, s1e2) = match s1es_arg with
    | [s1e1; s1e2] -> (s1e1, s1e2)
    | _ -> error_of_deadcode "sexp1_trans_tr_up: 1" in
  let (refval, s1e1) = match s1e1.sexp1_node with
    | SE1invar (refval, _, [s1e]) -> (refval, s1e)
    | _ -> begin
	PR.eprintf "%a: sexp1_trans_tr_up: illegal format\n" Loc.fprint loc0;
	Err.abort ()
      end in
  let s2t = if refval = 0 then srt2_view else srt2_viewt0ype in
  let s2e1 = sexp1_tr_dn s1e1 s2t and s2e2 = sexp1_tr_dn s1e2 s2t in
    sexp2_refarg refval s2e1 s2e2
(* end of [sexp1_trans_tr_up] *)

(* ****** ****** *)

and sexp1_id_tr_up (loc0: loc) (qid: Syn.squal_opt_id): sexp2 =
  match sexp2_env_oqfind qid with
    | Some s2i -> begin match s2i with
	| SI2cst s2cs -> begin match s2cs with
	    | s2c :: _ -> sexp2_cst s2c 
	    | [] -> sexp1_id_tr_up_errmsg_2 loc0 qid
	  end
	| SI2datcon d2c -> sexp1_app_datcon_tr_up loc0 d2c []
	| SI2var s2v -> sexp2_var s2v
	| SI2fil _ -> sexp1_id_tr_up_errmsg_3 loc0 qid
	| SI2mod _ -> sexp1_id_tr_up_errmsg_4 loc0 qid
      end
    | None -> sexp1_id_tr_up_errmsg_1 loc0 qid
(* end of [sexp1_id_tr_up] *)

and sexp1_struct_tr_up (ls1es: labsexp1 list): sexp2 =
  let (is_lin, is_prf, ls2es) = labsexp1_list_tr_up ls1es in
  let s2t = if is_lin then srt2_viewt0ype else srt2_t0ype in
    sexp2_struct_new_with_sort s2t ls2es
(* end of [sexp1_struct_tr_up] *)

and sexp1_tyrec_tr_up
  (is_flat: bool) (ls1es: labsexp1 list): sexp2 =
  let (is_lin, is_prf, ls2es) = match ls1es with
    | _ :: _ -> labsexp1_list_tr_up ls1es
    | [] -> (false, false, []) in
  let k = tyrec_kind_of_flatness is_flat in
  let s2t = srt2_tyrec is_flat is_lin is_prf in
  let s2t = 
    if is_flat then begin
      match tyrec_is_singleton 0 ls2es with
	| Some s2e -> srt2_singleton is_lin s2e | None -> s2t
    end else begin
      s2t
    end in begin
      sexp2_tyrec_with_sort s2t k 0 (*npf*) ls2es
    end
(* end of [sexp1_tyrec_tr_up] *)

and sexp1_tytup_tr_up
  (is_flat: bool) (npf: int) (s1es: sexp1 list): sexp2 =
  let rec aux (is_lin: bool) (is_prf: bool) (s2es: sexp2 list) = function
    | s1e :: s1es ->
	let s2e = sexp1_tr_dn_impredicative s1e in
	let s2t = s2e.sexp2_sort in
	let is_lin = is_lin || srt2_is_linear s2t in
	let is_prf = is_prf && srt2_is_proof s2t in
	  aux is_lin is_prf (s2e :: s2es) s1es
    | [] -> (is_lin, is_prf, List.rev s2es) in
  let (is_lin, is_prf, s2es) = match s1es with
    | _ :: _ -> aux false true [] s1es
    | [] -> (false, false, []) in
  let s2t = srt2_tyrec is_flat is_lin is_prf in
  let s2t = 
    if is_flat then begin
      match tytup_is_singleton npf s2es with
	| Some s2e -> srt2_singleton is_lin s2e | None -> s2t
    end else begin
      s2t
    end in begin
      sexp2_tytup_with_sort s2t is_flat npf s2es
    end
(* end of [sexp1_tytup_tr_up] *)

and sexp1_union_tr_up
  (s1e: sexp1) (ls1es: labsexp1 list): sexp2 =
  let s2e = sexp1_tr_dn s1e srt2_int in
  let (is_lin, is_prf, ls2es) = labsexp1_list_tr_up ls1es in
  let s2t = if is_lin then srt2_viewt0ype else srt2_t0ype in
    sexp2_union_with_sort s2t s2e ls2es
(* end of [sexp1_union_tr_up] *)

and sexp1_list_tr_up (s1es: sexp1 list): sexp2 list =
  List.map sexp1_tr_up s1es

and sexp1_opt_tr_up (os1e: sexp1 option): sexp2 option = begin
  match os1e with Some s1e -> Some (sexp1_tr_up s1e) | None -> None
end (* end of [sexp1_opt_tr_up] *)

(* ****** ****** *)

and labsexp1_list_tr_up
  (ls1es: labsexp1 list): bool * bool * labsexp2 list =
  let rec aux is_lin is_prf res = function
    | (l, os1ess, s1e) :: ls1es ->
	let s2e = sexp1_tr_dn_impredicative s1e in
	let s2e = match os1ess with
	  | Some s1ess ->
	      let f s1e = sexp1_tr_dn s1e srt2_int in
	      let s2ess = List.map (List.map f) s1ess in
		sexp2_tyarr s2e s2ess
	  | None -> s2e in
	let s2t = s2e.sexp2_sort in
	let is_lin = is_lin || srt2_is_linear s2t in
	let is_prf = is_prf && srt2_is_proof s2t in
	let res = (l, s2e) :: res in aux is_lin is_prf res ls1es
    | [] -> (is_lin, is_prf, List.rev res) in
    aux false true [] ls1es
(* end of [labsexp1_list_tr_up] *)

(* ****** ****** *)

and sexp1_tr_dn (s1e: sexp1) (s2t: srt2): sexp2 =
  match s1e.sexp1_node with
    | SE1extype name -> sexp2_extype s2t name
    | _ -> begin
	let s2e = sexp1_tr_up s1e in
	let s2t_s2e = s2e.sexp2_sort in
	  if srt2_leq s2t_s2e s2t then s2e else
	    sexp1_tr_dn_errmsg_1 s1e.sexp1_loc s2e.sexp2_sort s2t
      end (* end of [_] *)
(* end of [sexp1_tr_dn] *)

and sexp1_list_tr_dn (loc: loc)
  (s1es: sexp1 list) (s2ts: srt2 list): sexp2 list =
  let rec aux s2es = function
    | s1e :: s1es, s2t :: s2ts ->
	let s2e = sexp1_tr_dn s1e s2t in aux (s2e :: s2es) (s1es, s2ts)
    | [], [] -> List.rev s2es
    | [], _ :: _ -> sexp1_list_tr_dn_errmsg_less loc
    | _ :: _, [] -> sexp1_list_tr_dn_errmsg_more loc in
    aux [] (s1es, s2ts)
(* end of [sexp1_list_tr_dn] *)

and sexp1_tr_dn_bool (s1e: sexp1): sexp2 = sexp1_tr_dn s1e srt2_bool
and sexp1_tr_dn_int (s1e: sexp1): sexp2 = sexp1_tr_dn s1e srt2_int
and sexp1_tr_dn_prop (s1e: sexp1): sexp2 = sexp1_tr_dn s1e srt2_prop
and sexp1_tr_dn_type (s1e: sexp1): sexp2 = sexp1_tr_dn s1e srt2_type
and sexp1_tr_dn_t0ype (s1e: sexp1): sexp2 = sexp1_tr_dn s1e srt2_t0ype
and sexp1_tr_dn_view (s1e: sexp1): sexp2 = sexp1_tr_dn s1e srt2_view
and sexp1_tr_dn_viewtype (s1e: sexp1): sexp2 = sexp1_tr_dn s1e srt2_viewtype
and sexp1_tr_dn_viewt0ype (s1e: sexp1): sexp2 = sexp1_tr_dn s1e srt2_viewt0ype

and sexp1_tr_dn_impredicative (s1e: sexp1): sexp2 =
  let s2e = sexp1_tr_up s1e in
    if srt2_is_impredicative s2e.sexp2_sort then s2e
    else sexp1_tr_dn_impredicative_errmsg s1e
(* end of [sexp1_tr_dn-impredicative] *)

and sexp1_arg_tr_dn_impredicative (s1e: sexp1): sexp2 =
  let s2e = sexp1_arg_tr_up s1e in
    if srt2_is_impredicative s2e.sexp2_sort then s2e
    else sexp1_arg_tr_dn_impredicative_errmsg s1e
(* end of [sexp1_arg_tr_dn_impredicative] *)
    
and sexp1_mod_tr (loc: loc)
  (ls2vs: labsvar2 list) (s2e: sexp2) (ls2es: labsexp2 list): sexp2 =			
  let (sub, s2vs) = labsexp2_list_bind loc ls2vs ls2es in
  let s2e = sexp2_subst sub s2e in
    sexp2_exi s2vs [] s2e
(* end of [sexp1_mod_tr] *)

and squas1_tr (squas1: squas1): svar2 list * sexp2 list =
  let rec aux (s2vs0: svar2 list)
    (s2es0: sexp2 list) (s1qs: squa1 list)
    : svar2 list * sexp2 list = match s1qs with
      | s1q :: s1qs -> begin match s1q with
	  | SQ1prop s1e ->
	      let s2e = sexp1_tr_dn_bool s1e in aux s2vs0 (s2e :: s2es0) s1qs
	  | SQ1vars (ids, s1te) ->
	      let s2te = srtext1_tr s1te in begin match s2te with
		| STE2srt s2t ->
		    let s2vs =
		      let f id = svar2_new_with_id id s2t in List.map f ids in
		    let () = SEnv2.sexp2_env_add_var_list s2vs in
		      aux (List.rev_append s2vs s2vs0) s2es0 s1qs
		| STE2sub (s2v, s2t, s2es) ->
		    let rec aux1 s2vs0 s2es0 = function
		      | id :: ids ->
			  let s2v' = svar2_new_with_id id s2t in
			  let () = SEnv2.sexp2_env_add_var s2v' in
			  let s2es' = sexp2_alpha_list s2v s2v' s2es in
			    aux1 (s2v' :: s2vs0) (s2es' @ s2es0) ids
		      | [] -> aux s2vs0 s2es0 s1qs in aux1 s2vs0 s2es0 ids
		end (* end of [SQ1vars] *)
	end (* end of [::] *)
      | [] -> (List.rev s2vs0, List.rev s2es0) in
    aux [] [] (squas1.squas1_node)
(* end of [squas1_tr] *)

and squas1_list_tr (s1qss: squas1 list): (svar2 list * sexp2 list) list =
  List.map squas1_tr s1qss

(* ****** ****** *)

and srtext1_tr (s1te: srtext1): srtext2 = begin
  match s1te.srtext1_node with
  | STE1srt s1t -> begin match s1t.srt1_node with
      | SRT1id id -> begin match srt2_env_find_id id with
	  | Some s2te -> s2te
	  | None -> srtext1_tr_errmsg_1 s1t.srt1_loc id
	end
      | _ -> STE2srt (srt1_tr s1t)
    end
  | STE1sub (id, s1te, s1es) ->
      let s2te = srtext1_tr s1te in
      let s2t = match s2te with
	| STE2srt s2t -> s2t
	| STE2sub (_, s2t, _) -> s2t in
      let s2v = svar2_new_with_id id s2t in
      let () = SEnv2.SEXP2env.push () in
      let () = SEnv2.sexp2_env_add_var s2v in
      let s2es = List.map sexp1_tr_dn_bool s1es in
      let () = SEnv2.SEXP2env.pop () in
      let s2es = match s2te with
	| STE2srt _ -> s2es
	| STE2sub (s2v', _, s2es') ->
	    s2es @ sexp2_alpha_list s2v' s2v s2es' in
	STE2sub (s2v, s2t, s2es)
end (* end of [srtext1_tr] *)

(* ****** ****** *)

let sarg1_tr ((id, os1t): sarg1): sarg2 = (id, srt1_opt_tr os1t)
let sarg1_list_tr (arg: sarg1 list): sarg2 list = List.map sarg1_tr arg

let svar1_tr (id, s1t): svar2 = let s2t = srt1_tr s1t in
  let s2v = svar2_new_with_id id s2t in (SEnv2.sexp2_env_add_var s2v; s2v)
(* end of [svar1_tr] *)

let svar1_list_tr (s1vs: svar1 list): svar2 list = List.map svar1_tr s1vs

(* ****** ****** *)

let sexparg1_tr (s1a: sexparg1): sexparg2 = begin
  match s1a with
  | SEXPARG1one -> SEXPARG2one
  | SEXPARG1all -> SEXPARG2all
  | SEXPARG1seq s1es -> SEXPARG2seq (sexp1_list_tr_up s1es)
end (* end of [sexparg1_tr] *)

let sexparg1_list_tr (s1as: sexparg1 list): sexparg2 list =
  List.map sexparg1_tr s1as

(* ****** ****** *)

let srt2_datakind (dtk: Syn.datakind): srt2 = begin
  match dtk with
    | Syn.DKprop -> srt2_prop
    | Syn.DKtype -> srt2_type
    | Syn.DKview -> srt2_view
    | Syn.DKviewtype -> srt2_viewtype
end (* en dof [srt2_datakind] *)

(* ****** ****** *)

let the_staload_level : int ref = ref 0
let staload_level_get () : int = !the_staload_level
let staload_level_inc (): unit =
  (the_staload_level := !the_staload_level + 1)
let staload_level_dec (): unit =
  (the_staload_level := !the_staload_level - 1)

type overloaditem =
  | OLIsymintr of (loc * Syn.did list)
  | OLIsymelim of (loc * Syn.did list)
  | OLIbind of (loc * Syn.did * ditem2)

let the_overload_list : (overloaditem list) ref = ref []

let overload_list_add_symintr
  (loc: loc) (names: Syn.did list): unit =
  the_overload_list := OLIsymintr (loc, names) :: !the_overload_list

let overload_list_add_symelim
  (loc: loc) (names: Syn.did list): unit =
  the_overload_list := OLIsymelim (loc, names) :: !the_overload_list

let overload_list_add_bind
  (loc: loc) (name: Syn.did) (d2i: ditem2): unit =
  the_overload_list := OLIbind (loc, name, d2i) :: !the_overload_list

let overload_list_get (): overloaditem list =
  List.rev (!the_overload_list)

let overload_list_reset (): unit = (the_overload_list := [])

(* ****** ****** *)

let rec pat1_of_pat1 (p1t: pat1): pat1 =
  match p1t.pat1_node with
    | PT1qid (None, id) -> begin
	match Env1.e0xp1_find_sym (Syn.sym_of_did id) with
	  | Some e -> pat1_of_pat1 (pat1_of_e0xp1 p1t.pat1_loc e)
	  | None -> p1t
      end
    | PT1qid (Some _, _) -> p1t
    | PT1app_sta (p1t1, s1as2) ->
	pat1_app_sta p1t.pat1_loc (pat1_of_pat1 p1t1) s1as2
    | _ -> p1t
(* end of [pat1_of_pat1] *)

let rec pat1_tr (p1t: pat1): pat2 =
  let loc = p1t.pat1_loc in match p1t.pat1_node with
    | PT1ann (p1t, s1e) ->
	let p2t = pat1_tr p1t in
	let s2e = sexp1_tr_dn_impredicative s1e in
	  pat2_ann loc p2t s2e

    | PT1any -> pat2_any loc
    | PT1anys -> pat2_any loc

    | PT1app_dyn (p1t1, np1ts2) -> begin
	let p1t1 = pat1_of_pat1 p1t1 in
	let loc1 = p1t1.pat1_loc in match p1t1.pat1_node with
	  | PT1qid qid -> begin
	      let is_vbox = match qid with
		| (None, id) -> Syn.did_is_vbox id | _ -> false in
		if is_vbox then pat1_vbox_tr loc np1ts2 else
		  pat1_app_dyn_tr loc loc1 loc1 qid [] np1ts2
	    end
	  | PT1app_sta (p1t1, s1as) -> begin
	      match p1t1.pat1_node with
		| PT1qid qid -> pat1_app_dyn_tr
		    loc p1t1.pat1_loc loc1 qid s1as np1ts2
		| _ -> pat1_tr_errmsg_1 p1t1
	    end
	  | _ -> pat1_tr_errmsg_2 p1t1
      end

    | PT1app_sta _ -> error_with_loc loc "ats_trans2: pat1_tr: PT1sapp"
	
    | PT1as (id, p1t) -> begin
	let d2v = dvar2_new_with_id loc id false (*is_fixed*) in
	  pat2_var_some loc false(*isref*) d2v (pat1_tr p1t)
      end

    | PT1char c -> pat2_char loc c

    | PT1exi (s1vs, p1t) ->
        let () = SEnv2.SEXP2env.push () in
	let s2vs = svar1_list_tr s1vs in
	let p2t = pat1_tr p1t in
        let () = SEnv2.SEXP2env.pop () in
	  pat2_exi loc s2vs p2t

    | PT1free p1t -> pat1_free_tr loc p1t

    | PT1int i -> pat2_int loc i

    | PT1list (npf, p1ts) -> begin match p1ts with
	| _ :: _ ->
	    let p2ts = pat1_list_tr p1ts in
	      pat2_tup loc true (* is_flat *) false (* is_omit *) npf p2ts
	| [] -> pat2_empty loc
      end

    | PT1lst p1ts -> let p2ts = pat1_list_tr p1ts in pat2_lst loc p2ts

    | PT1qid qid -> begin
	let (odq, id) = qid in match odq with
	  | Some _ -> pat1_app_dyn_tr loc loc loc qid [] (0, [])
	  | None -> begin
	      match Env1.e0xp1_find_sym (Syn.sym_of_did id) with
		| Some e -> pat1_tr (pat1_of_e0xp1 loc e)
		| None -> begin
		    if Syn.did_is_true id then pat2_bool loc true
		    else if Syn.did_is_false id then pat2_bool loc false
		    else begin
		      let d2v = dvar2_new_with_id loc id false in
			pat2_var_none loc false(*isref*) d2v
		    end
		  end
	    end
      end

    | PT1rec (is_flat, is_omit, lp1ts) ->
	let lp2ts = labpat1_list_tr lp1ts in
	  pat2_rec loc is_flat is_omit 0 (* npf *) lp2ts

    | PT1ref id -> begin
	let d2v = dvar2_new_with_id loc id false in
	  pat2_var_none loc true(*isref*) d2v
      end

    | PT1refas (id, p1t) -> begin
	let d2v = dvar2_new_with_id loc id false (*is_fixed*) in
	  pat2_var_some loc true(*isref*) d2v (pat1_tr p1t)
      end

    | PT1string s -> pat2_string loc s

    | PT1tup (is_flat, (npf, p1ts)) ->
	let p2ts = pat1_list_tr p1ts in
	  pat2_tup loc is_flat false (* is_omit *) npf p2ts

    | _ -> begin
	PR.fprintf stderr "%a: pat1_tr: %a: yet to be implemented!"
	  Loc.fprint loc fprint_pat1 p1t;
	prerr_newline ();
	Err.abort ();
      end
(* end of [pat1_tr] *)

and pat1_list_tr (p1ts: pat1 list): pat2 list =
   List.map pat1_tr p1ts

and labpat1_list_tr (lp1ts: labpat1 list): labpat2 list =
   List.map (function (l, p1t) -> (l, pat1_tr p1t)) lp1ts

and pat1_app_dyn_tr (loc_dap: loc) (loc_sap: loc) (loc_id: loc)
  (qid: Syn.dqual_opt_id) (s1as: svararg1 list) (np1ts: int_pat1_list): pat2 =
  let d2cs = match dexp2_env_oqfind qid with
    | Some (DI2con d2cs) -> d2cs
    | Some _ -> pat1_app_dyn_tr_errmsg_2 loc_id qid
    | None -> pat1_app_dyn_tr_errmsg_1 loc_id qid in
  let (npf, p1ts) = np1ts in
  let is_arg_omit = match p1ts with
    | [p1t] -> begin
	match p1t.pat1_node with PT1anys -> true | _ -> false
      end
    | _ -> false in
  let d2c = 
    let d2cs =
      if is_arg_omit then d2cs else
	dcon2_select_with_arity d2cs (List.length p1ts) in
      match d2cs with
	| [d2c] -> d2c
	| _ -> pat1_app_dyn_tr_errmsg_3 loc_id qid in
  let p1ts =
    if is_arg_omit then begin match p1ts with
      | [p1t] ->
	  let (npf_con, s2es) = d2c.dcon2_arg in
	  let f s2e = pat1_any p1t.pat1_loc in List.map f s2es
      | _ -> p1ts (* deadcode *)
    end else p1ts in
    pat1_con_tr loc_dap loc_sap d2c s1as (npf, p1ts)
(* end of [pat1_app_dyn_tr] *)

(* ****** ****** *)

and pat1_arg_tr (p1t0: pat1): pat2 =
  let loc0 = p1t0.pat1_loc in match p1t0.pat1_node with
    | PT1ann (p1t, s1e) ->
	let p2t = pat1_tr p1t in
	let s2e = sexp1_arg_tr_dn_impredicative s1e in
	  pat2_ann loc0 p2t s2e
    | PT1list (npf, p1ts) ->
	let p2ts = pat1_arg_list_tr p1ts in
	  pat2_list loc0 (npf, p2ts)
    | _ -> pat1_tr p1t0
(* end of [pat1_arg_tr] *)

and pat1_arg_list_tr (p1ts: pat1 list): pat2 list =
  List.map pat1_arg_tr p1ts

(* ****** ****** *)

and pat1_con_tr_aux1 d2c s2vss s2ess sub qua
  : svar2 list list * sexp2 list list * sexp2 =
  match qua with
    | (s2vs, s2es) :: qua -> begin
	let (sub, s2vs) = subst_extend sub s2vs in
	let s2es = sexp2_list_subst sub s2es in
	  pat1_con_tr_aux1 d2c (s2vs :: s2vss) (s2es :: s2ess) sub qua
      end
    | [] -> begin
	let (npf, s2es_arg) = d2c.dcon2_arg in
	let s2es_arg = sexp2_list_subst sub s2es_arg in
	let s2e_res = match d2c.dcon2_ind with
	  | Some s2es_ind ->
	      let s2es_ind = sexp2_list_subst sub s2es_ind in
		sexp2_cstapp d2c.dcon2_scst s2es_ind
	  | None -> sexp2_cst d2c.dcon2_scst in
	let s2vss = List.rev s2vss in
	let s2pss = List.rev s2ess in
	  (s2vss, s2pss, sexp2_fun_con (npf, s2es_arg) s2e_res)
      end
(* end of [pat1_con_tr_aux1] *)

and pat1_con_tr_aux2 loc_sap d2c s2vss s2ess sub qua s1as
  : svar2 list list * sexp2 list list * sexp2 =
  match s1as with
    | SVARARG1one :: s1as -> begin match qua with
	| (s2vs, s2es) :: qua ->
	    let (sub, s2vs) = subst_extend sub s2vs in
	    let s2es = sexp2_list_subst sub s2es in
	      pat1_con_tr_aux2 loc_sap d2c
		(s2vs :: s2vss) (s2es :: s2ess) sub qua s1as
	| [] -> pat1_con_tr_errmsg_1 loc_sap d2c
      end
    | SVARARG1all :: s1as -> pat1_con_tr_aux1 d2c s2vss s2ess sub qua
    | SVARARG1seq arg :: s1as -> begin match qua with
	| (s2vs, s2es) :: qua ->
	    let arg = sarg1_list_tr arg in
	    let (sub, s2vs) =
	      subst_extend_with_arg loc_sap sub arg s2vs in
	    let s2es = sexp2_list_subst sub s2es in
	      pat1_con_tr_aux2 loc_sap d2c
		(s2vs :: s2vss) (s2es :: s2ess) sub qua s1as
	| [] -> pat1_con_tr_errmsg_1 loc_sap d2c
      end
    | [] -> pat1_con_tr_aux1 d2c s2vss s2ess sub qua
(* end of [pat1_con_tr_aux2] *)

and pat1_con_tr_inst
  (loc_sap: loc) (d2c: dcon2) (s1as: svararg1 list)
  : svar2 list list * sexp2 list list * sexp2 =
  pat1_con_tr_aux2 loc_sap d2c [] [] [] d2c.dcon2_qua s1as

and pat1_con_tr (loc_dap: loc) (loc_sap: loc)
  (d2c: dcon2) (s1as: svararg1 list) (np1ts: int_pat1_list): pat2 =
  let (s2vss, s2ess, s2e) = pat1_con_tr_inst loc_sap d2c s1as in
  let (npf, p1ts) = np1ts in
  let p2ts = pat1_list_tr p1ts in
    pat2_con loc_dap 1(*freeknd*) d2c s2vss s2ess s2e (npf, p2ts)
(* end of [pat1_con_tr] *)

and pat1_free_tr loc (p1t: pat1): pat2 = begin
  let p2t = pat1_tr p1t in match p2t.pat2_node with
    | PT2con (freeknd, d2c, s2vss, s2pss, s2e, np2ts) -> begin
	pat2_con loc (-freeknd) d2c s2vss s2pss s2e np2ts
      end
    | _ -> pat1_free_tr_errmsg_1 loc
end (* end of pat1_free_tr *)

(* ****** ****** *)

and pat1_vbox_tr loc (np1ts: int_pat1_list): pat2 =
  let (npf, p1ts) = np1ts in
  let p2t = match p1ts with
    | [p1t] -> pat1_tr p1t
    | _ -> begin
	PR.fprintf stderr "%a: exactly one pattern is required.\n"
	  Loc.fprint loc;
	Err.abort ();
      end in
    match p2t.pat2_node with
      | PT2var (false(*isref*), d2v, None) -> pat2_vbox loc d2v
      | _ -> begin
	  PR.fprintf stderr
	    "%a: the argument of vbox needs to be a dynamic variable.\n"
	    Loc.fprint p2t.pat2_loc;
	  Err.abort ();
	end (* end of [_] *)
(* end of [pat1_vbox_tr] *)

(* ****** ****** *)

let rec dexp1_of_dexp1 (d1e: dexp1): dexp1 = begin
  match d1e.dexp1_node with
    | DE1qid (None, id) -> begin
	match Env1.e0xp1_find_sym (Syn.sym_of_did id) with
	  | Some e -> dexp1_of_e0xp1 d1e.dexp1_loc e | None -> d1e
      end
    | DE1qid _ -> d1e (* qualified id *)
    | DE1app_sta (d1e1, s1as2) ->
	dexp1_app_sta d1e.dexp1_loc (dexp1_of_dexp1 d1e1) s1as2
    | _ -> d1e
end (* end of [dexp1_of_dexp1] *)

let dlab1_of_dexp1 (d1e0: dexp1): dlab1 option =
  match d1e0.dexp1_node with
    | DE1arrsub (d1e_arr, d1ess_ind) -> begin
	match d1e_arr.dexp1_node with
	  | DE1qid (None, id) ->
	      let l = Lab.make_with_symbol (Syn.sym_of_did id) in
		Some (dlab1_of_lab_ind (Some l) (Some d1ess_ind))
	  | _ -> None
      end
    | DE1int (Syn.IKint, i) ->
	let l = Lab.make_with_intinf i in
	  Some (dlab1_of_lab_ind (Some l) None)
    | DE1qid (None, id) ->
	let l = Lab.make_with_symbol (Syn.sym_of_did id) in
	  Some (dlab1_of_lab_ind (Some l) None)
    | _ -> None
(* end of [dlab1_of_dexp1] *)

let rec dexp1_tr (d1e0: dexp1): dexp2 =
(*
  let () = PR.fprintf stdout "dexp1_tr: d1e0 = %a\n" fprint_dexp1 d1e0 in
*)
  let loc = d1e0.dexp1_loc in match d1e0.dexp1_node with
    | DE1ann_type (d1e, s1e) -> begin
	let d2e = dexp1_tr d1e and s2e = sexp1_tr_dn_impredicative s1e in
	  dexp2_ann_type loc d2e s2e
      end (* end of [DE1ann_type] *)

    | DE1ann_effc (d1e, effc) -> begin
	let d2e = dexp1_tr d1e and sf2e = effcst_tr loc effc in
	  dexp2_ann_seff loc d2e sf2e
      end (* end of [DE1ann_effc] *)

    | DE1ann_funclo (d1e, fc) -> begin
	let d2e = dexp1_tr d1e in dexp2_ann_funclo loc d2e fc
      end (* end of [DE1ann_funclo] *)

    | DE1app_dyn (d1e, (npf, d1es)) -> begin
	let d1e = dexp1_of_dexp1 d1e in (* resolving defined symbol *)
	  begin match d1e.dexp1_node with
	    | DE1qid qid -> begin
		let loc_id = d1e.dexp1_loc in
		  match specdid_of_dqual_opt_id qid with
		    | SDassgn -> dexp1_assgn_tr loc d1es
		    | SDderef -> dexp1_deref_tr loc d1es
		    | SDnone -> dexp1_app_dyn_id_tr
			loc loc_id loc_id qid [] npf d1es
	      end
	    | DE1app_sta (d1e1, s1as2) -> begin
		match d1e1.dexp1_node with
		  | DE1qid qid ->
		      let loc_sap = d1e.dexp1_loc and loc_id = d1e1.dexp1_loc in
			dexp1_app_dyn_id_tr loc loc_sap loc_id qid s1as2 npf d1es
		  | _ -> dexp1_app_dyn_tr loc d1e npf d1es
	      end
	    | _ -> dexp1_app_dyn_tr loc d1e npf d1es
	  end
      end (* end of [DE1app_dyn] *)

    | DE1app_sta (d1e1, s1as2) -> begin
	let d1e1 = dexp1_of_dexp1 d1e1 in (* resolving defined symbol *)
	  begin match d1e1.dexp1_node with
	    | DE1qid qid -> dexp1_app_sta_id_tr loc d1e1.dexp1_loc qid s1as2
	    | _ -> dexp1_app_sta_tr loc d1e1 s1as2
	  end
      end (* end of [DE1app_sta] *)

    | DE1arr (s1e, d1es) -> begin
	let s2e = sexp1_tr_dn_viewt0ype s1e in
	let d2es = dexp1_list_tr d1es in dexp2_arr loc s2e d2es
      end (* end of [DE1arr] *)

    | DE1arrsub (root, offset) -> dexp1_arrsub_tr loc root offset

    | DE1case (sgn, osty1, d1e, c1ls) -> begin (* sgn: -1/0/1 *)
	let osty2 = statype1_opt_tr loc osty1 in
	let d2es = match d1e.dexp1_node with
	  | DE1list (npf, d1es) -> dexp1_list_tr d1es
	  | _ -> let d2e = dexp1_tr d1e in [d2e] in
	let n = List.length d2es in
	let c2ls = cla1_list_tr n c1ls in
	  dexp2_case loc sgn osty2 d2es c2ls
      end (* end of [DE1case] *)

    | DE1char c -> dexp2_char loc c

    | DE1crypt (knd, d1e) -> dexp2_crypt loc knd (dexp1_tr d1e)

    | DE1delay (d1e) -> dexp2_delay loc (dexp1_tr d1e)

    | DE1demac (d1e) -> dexp2_demac loc (dexp1_tr d1e)

    | DE1dynload (name) -> dexp2_dynload loc name

    | DE1effmask (eff, d1e) -> dexp2_effmask loc eff (dexp1_tr d1e)

    | DE1empty -> dexp2_empty loc

    | DE1enmac (d1e) -> dexp2_enmac loc (dexp1_tr d1e)

    | DE1exi (s1a, d1e) -> begin
        dexp2_exi loc (sexparg1_tr s1a) (dexp1_tr d1e)
      end (* end of [DE1exi] *)

    | DE1extval (s1e, code) -> begin
	dexp2_extval loc (sexp1_tr_dn_viewt0ype s1e) code
      end (* end of [DE1extval] *)
	
    | DE1fix (id, d1e) -> begin
	let d2v = dvar2_new_with_id loc id true (* is_fixed *) in
	let () = SDEnv2.DEXP2env.push () in
	let () = SDEnv2.dexp2_env_add_var d2v in
	let d2e = dexp1_tr d1e in
	let () = SDEnv2.DEXP2env.pop () in dexp2_fix loc d2v d2e
      end (* end of [DE1fix] *)

    | DE1float f -> dexp2_float loc f

    | DE1fold (qid, d1e) -> begin match sexp2_env_oqfind qid with
	| Some (SI2cst s2cs) -> begin match s2cs with
	    | s2c :: _ -> dexp2_fold loc s2c (dexp1_tr d1e)
	    | [] -> error_of_deadcode "ats_trans2: dexp1_tr: DE1fold"
	  end
	| _ -> dexp1_tr_errmsg_1 loc qid
      end (* end of [DE1fold] *)

    | DE1foldat (s1as, d1e) -> begin
	let s2as = sexparg1_list_tr s1as in
	let d2e = dexp1_tr d1e in dexp2_foldat loc s2as d2e
      end (* end of [DE1foldat] *)

    | DE1freeat (s1as, d1e) -> begin
	let s2as = sexparg1_list_tr s1as in
	let d2e = dexp1_tr d1e in dexp2_freeat loc s2as d2e
      end (* end of [DE1freeat] *)

    | DE1for (oinv1, (init1, test1, post1), body1) -> begin
	let init2 = dexp1_tr init1 in
	let () = SEnv2.SEXP2env.push () in
	let oinv2 = loopinv1_opt_tr oinv1 in
	let test2 = dexp1_tr test1 in
	let post2 = dexp1_tr post1 in
	let body2 = dexp1_tr body1 in
	let () = SEnv2.SEXP2env.pop () in
	  dexp2_for loc oinv2 init2 test2 post2 body2
      end (* end of [DE1for] *)

    | DE1if (osty1, d1e1, d1e2, od1e3) -> begin
	let osty2 = statype1_opt_tr loc osty1 in
	let d2e1 = dexp1_tr d1e1 in let d2e2 = dexp1_tr d1e2 in
	let od2e3 = dexp1_opt_tr od1e3 in
	  dexp2_if loc osty2 d2e1 d2e2 od2e3
      end (* end of [DE1if] *)

    | DE1int (ik, i) -> dexp2_int loc ik i

    | DE1lam_dyn (is_lin, p1t, d1e) -> begin
(*
	let () =
	  PR.fprintf stdout "dexp1_tr: DE1lam_dyn: p1t = %a\n" fprint_pat1 p1t in
	let () =
	  PR.fprintf stdout "dexp1_tr: DE1lam_dyn: d1e = %a\n" fprint_dexp1 d1e in
*)
	let p2t = pat1_arg_tr p1t in
	let np2ts = match p2t.pat2_node with
	  | PT2list np2ts -> np2ts | _ -> (0, [p2t]) in
	let () = SDEnv2.stadynenv2_push () in
	let () = SEnv2.sexp2_env_add_var_list p2t.pat2_svs in
	let () = SDEnv2.dexp2_env_add_var_list p2t.pat2_dvs in
	let d2e = dexp1_tr d1e in
	let () = SDEnv2.stadynenv2_pop () in
	  dexp2_lam_dyn loc is_lin np2ts d2e
      end (* end of [DE1lam_dyn] *)

    | DE1lam_met (s1es, d1e) -> begin
	let s2es = sexp1_list_tr_up s1es in
	let d2e = dexp1_tr d1e in dexp2_lam_met_new loc s2es d2e
      end (* end of [DE1lam_met] *)
	    
    | DE1lam_sta_ana _ -> dexp1_tr_errmsg_lam_sta_ana loc

    | DE1lam_sta_syn (squas1, d1e) -> begin
	let () = SEnv2.SEXP2env.push () in
	let (s2vs, s2es) = squas1_tr squas1 in
	let d2e = dexp1_tr d1e in
	let () = SEnv2.SEXP2env.pop () in
	  dexp2_lam_sta loc s2vs s2es d2e
      end (* end of [DE1lam_sta_syn] *)

    | DE1lam_sta_para (squas1, d1e) -> begin
	let () = SEnv2.SEXP2env.push () in
	let (s2vs, s2es) = squas1_tr squas1 in
	let d2e = dexp1_tr d1e in
	let () = SEnv2.SEXP2env.pop () in
	  dexp2_lam_sta_para loc s2vs s2es d2e
      end (* end of [DE1lam_sta_para] *)

    | DE1let (d1cs, d1e) -> begin
	let () = push_all () in
	let d2cs = dec1_list_tr d1cs in
	let d2e = dexp1_tr d1e in
	let () = pop_all () in dexp2_let loc d2cs d2e
      end (* end of [DE1let] *)

    | DE1list (npf, d1es) -> begin match d1es with
	| _ :: _ -> begin
	    let d2es = dexp1_list_tr d1es in
	      dexp2_tup loc true (* is_flat *) npf d2es
          end (* end of [::] *)
	| [] -> dexp2_empty loc
      end (* end of [DE1list] *)

    | DE1loopexn i -> dexp2_loopexn loc i

    | DE1lst d1es -> dexp2_lst loc (dexp1_list_tr d1es)
	
    | DE1mod (m1ids) -> dexp2_mod loc (mid1_list_tr m1ids)

    | DE1qid ((None, id) as qid) -> begin
	let oe = Env1.e0xp1_find_sym (Syn.sym_of_did id) in
	  match oe with
	    | Some e -> dexp1_tr (dexp1_of_e0xp1 loc e)
	    | None -> dexp1_id_tr loc qid
      end (* end of [DE1qid] *)

    | DE1qid qid (* qualified id *) -> dexp1_id_tr loc qid

    | DE1ptrof d1e -> dexp2_ptrof loc (dexp1_tr d1e)

    | DE1raise (d1e) -> dexp2_raise loc (dexp1_tr d1e)

    | DE1rec (is_flat, ld1es) -> begin
	let ld2es = labdexp1_list_tr ld1es in
	  dexp2_rec loc is_flat 0 (* npf *) ld2es
      end (* end of [DE1rec] *)
	  
    | DE1sel (is_ptr, d1e, d1l) -> begin
	dexp2_sel_1 loc is_ptr (dexp1_tr d1e) (dlab1_tr d1l)
      end (* end of [DE1sel] *)

    | DE1seq d1es -> dexp2_seq loc (dexp1_list_tr d1es)

    | DE1sif (s1e_cond, d1e_then, d1e_else) -> begin
	let s2e_cond = sexp1_tr_dn_bool s1e_cond in
	let d2e_then = dexp1_tr d1e_then in let d2e_else = dexp1_tr d1e_else in
	  dexp2_sif loc s2e_cond d2e_then d2e_else
      end (* end of [DE1sif] *)

    | DE1string s -> dexp2_string loc s

    | DE1struct ld1es ->
	dexp2_struct loc (labdexp1_list_tr ld1es)

    | DE1template (qid, s1ess) ->
	let d2e = dexp1_id_tr loc qid in
	let s2ess = List.map sexp1_list_tr_up s1ess in
(*
	let () = PR.fprintf stdout
          "dexp1_tr: DE1template: s2ess = %a\n" fprint_sexp2_list_list s2ess in
*)
	  dexp2_template loc d2e s2ess

    | DE1top -> dexp2_top loc

    | DE1trywith (d1e, c1ls) -> begin
	let d2e = dexp1_tr d1e in let c2ls = cla1_list_tr 1 c1ls in
	  dexp2_trywith loc d2e c2ls
      end (* end of [DE1trywith] *)

    | DE1tup (is_flat, (npf, d1es)) -> begin
	let d2es = dexp1_list_tr d1es in dexp2_tup loc is_flat npf d2es
      end (* end of [DE1tup] *)

    | DE1unfold (qid, d1e) -> begin
	match sexp2_env_oqfind qid with
	  | Some (SI2cst s2cs) -> begin match s2cs with
	      | [s2c] -> dexp2_unfold loc s2c (dexp1_tr d1e)
	      | _ -> dexp1_tr_errmsg_2 loc qid
	    end
	  | _ -> dexp1_tr_errmsg_1 loc qid
      end (* end of [DE1unfold] *)

    | DE1viewat d1e -> dexp2_viewat loc (dexp1_tr d1e)

    | DE1where (d1e, d1cs) -> begin
	let () = push_all () in
	let d2cs = dec1_list_tr d1cs in
	let d2e = dexp1_tr d1e in
	let () = pop_all () in dexp2_let loc d2cs d2e
      end (* DE1where *)

    | DE1while (oinv1, test, body) -> begin
	let () = SEnv2.SEXP2env.push () in
	let oinv2 = loopinv1_opt_tr oinv1 in
	let test = dexp1_tr test in let body = dexp1_tr body in
	let () = SEnv2.SEXP2env.pop () in dexp2_while loc oinv2 test body
      end (* end of [DE1while] *)

    | _ -> begin
	PR.fprintf stderr "%a: dexp1_tr: d1e0 =  %a\n"
	  Loc.fprint loc fprint_dexp1 d1e0;
	Err.abort ();
      end (* end of [_] *)
(* end of [dexp1_tr] *)

and dexp1_list_tr (d1es: dexp1 list): dexp2 list =
  List.map dexp1_tr d1es

and dexp1_list_list_tr (d1ess: dexp1 list list): dexp2 list list =
  List.map dexp1_list_tr d1ess

and dexp1_opt_tr (od1e: dexp1 option): dexp2 option =
  match od1e with Some d1e -> Some (dexp1_tr d1e) | None -> None

and labdexp1_tr ((l, d1e): labdexp1): labdexp2 = (l, dexp1_tr d1e)

and labdexp1_list_tr (ld1es: labdexp1 list): labdexp2 list =
  List.map labdexp1_tr ld1es

and dlab1_tr (d1l: dlab1): dlab2 =
  let ind2 = match d1l.dlab1_ind with
    | Some d1ess -> Some (dexp1_list_list_tr d1ess)
    | None -> None in
    dlab2_lab_ind d1l.dlab1_lab ind2

(* ****** ****** *)

and dexp1_id_tr (loc: loc) (qid: Syn.dqual_opt_id): dexp2 =
  match dexp2_env_oqfind qid with
    | Some d2i -> begin match d2i with
	| DI2con d2cs -> begin
	    let d2cs = dcon2_select_with_arity d2cs 0 in
	      match d2cs with
		| [d2c] -> dexp2_con loc d2c [] 0 []
		| _ -> dexp1_id_tr_errmsg_1 loc qid
	    end
	| DI2cst d2c -> dexp2_cst loc d2c
	| DI2mac d2m ->
	    let d2e = dexp2_dmac loc d2m in
	      if d2m.dmac2_abbrev then dexp2_demac loc d2e else d2e
	| DI2sym d2is -> dexp2_sym loc (dsym2_make loc qid d2is)
	| DI2var d2v -> dexp2_var loc d2v
      end
    | None -> dexp1_id_tr_errmsg_2 loc qid
(* end of [dexp1_id_tr] *)

(* ****** ****** *)

and dexp1_arrsub_tr (loc: loc)
  (d1e_root: dexp1) (d1ess_ind: dexp1 list list): dexp2 =
  let d2s_brackets = dsym2_brackets loc in
(*
  let () =
    PR.fprintf stdout "dexp1_arrsub_tr: d2is = %a\n"
      fprint_ditem2_list d2s_brackets.dsym2_item in
*)
  let d2e_root = dexp1_tr d1e_root in
  let d2ess_ind = List.map dexp1_list_tr d1ess_ind in
    dexp2_arrsub loc d2s_brackets d2e_root d2ess_ind
(* end of [dexp1_arrsub_tr] *)

(* ****** ****** *)

and dexp1_assgn_tr (loc: loc) (d1es: dexp1 list): dexp2 =
  match d1es with
    | [d1e1; d1e2] -> dexp2_assgn loc (dexp1_tr d1e1) (dexp1_tr d1e2)
    | _ -> dexp1_assgn_tr_errmsg_1 loc

and dexp1_deref_tr (loc: loc) (d1es: dexp1 list): dexp2 =
  match d1es with
    | [d1e] -> dexp2_deref loc (dexp1_tr d1e)
    | _ -> dexp1_deref_tr_errmsg_1 loc

and dexp1_selptr_tr (loc: loc) (d1es: dexp1 list): dexp2 =
  match d1es with
    | [d1e1; d1e2] -> begin
	let d1l = match dlab1_of_dexp1 d1e2 with
	  | Some d1l -> d1l
	  | None -> dexp1_selptr_tr_errmsg_1 d1e2 in
	  dexp2_selptr loc (dexp1_tr d1e1) (dlab1_tr d1l)
      end
    | _ -> dexp1_selptr_tr_errmsg_2 loc
(* end of [dexp1_selptr_tr] *)

(* ****** ****** *)

and dexp1_app_sta_id_tr (loc_sap: loc) (loc_id: loc)
  (qid: Syn.dqual_opt_id) (s1as: sexparg1 list): dexp2 =
  let s2as = sexparg1_list_tr s1as in
    match dexp2_env_oqfind qid with
      | Some (DI2con d2cs) -> begin
	  let d2cs = dcon2_select_with_arity d2cs 0 in
	    match d2cs with
	      | [d2c] -> dexp2_con loc_sap d2c s2as 0 []
	      |  _ -> dexp1_app_sta_id_tr_errmsg_1 loc_id qid
	end

      | Some (DI2cst d2c) ->
	  dexp2_app_sta loc_sap (dexp2_cst loc_id d2c) s2as

      | Some (DI2var d2v) ->
	  dexp2_app_sta loc_sap (dexp2_var loc_id d2v) s2as

      | _ -> dexp1_app_sta_id_tr_errmsg_2 loc_id qid
(* end of [dexp1_app_sta_id_tr] *)

and dexp1_app_sta_tr (loc: loc) (d1e: dexp1) (s1as: sexparg1 list): dexp2 =
  dexp2_app_sta loc (dexp1_tr d1e) (sexparg1_list_tr s1as)

(* ****** ****** *)

and dexp1_app_dyn_id_tr (loc_dap: loc) (loc_sap: loc) (loc_id: loc)
  (qid: Syn.dqual_opt_id) (s1as: sexparg1 list) (npf: int) (d1es: dexp1 list): dexp2 =
  let s2as = sexparg1_list_tr s1as in
  let d2es = dexp1_list_tr d1es in
    match dexp2_env_oqfind qid with
      | Some (DI2con d2cs) -> begin
	  let n = List.length d2es in    
	  let d2cs = dcon2_select_with_arity d2cs n in
	    match d2cs with
	      | [d2c] -> dexp2_con loc_dap d2c s2as npf d2es
	      |  _ -> dexp1_app_dyn_id_tr_errmsg_1 loc_id qid
	end

      | Some (DI2cst d2c) ->
	  let d2e =
	    dexp2_app_sta loc_sap (dexp2_cst loc_id d2c) s2as in
	    dexp2_app_dyn loc_dap d2e npf d2es

      | Some (DI2mac d2m) ->
	  let d2e = dexp2_dmac loc_id d2m in
	    dexp2_app_dyn loc_dap d2e npf d2es

      | Some (DI2var d2v) ->
	  let d2e = dexp2_app_sta loc_sap (dexp2_var loc_id d2v) s2as in
	    dexp2_app_dyn loc_dap d2e npf d2es

      | Some (DI2sym d2is) ->
	  let d2s = dsym2_make loc_id qid d2is in
	  let d2e = dexp2_app_sta loc_sap (dexp2_sym loc_id d2s) s2as in
	    dexp2_app_dyn loc_dap d2e npf d2es

      | None -> dexp1_app_dyn_id_tr_errmsg_2 loc_id qid
(* end of [dexp1_app_dyn_id_tr] *)

and dexp1_app_dyn_tr (loc: loc)
  (d1e_fun: dexp1) (npf: int) (d1es_arg: dexp1 list): dexp2 =
  let d2e_fun = dexp1_tr d1e_fun in
  let d2es_arg = dexp1_list_tr d1es_arg in
    dexp2_app_dyn loc d2e_fun npf d2es_arg
(* end of [dexp1_app_dyn_tr] *)

(* ****** ****** *)

and dexp1_tr_dn (d1e0: dexp1) (s2e0: sexp2): dexp2 =
  let loc = d1e0.dexp1_loc in match s2e0.sexp2_node with
    | SE2uni (s2vs, s2ps, s2e) -> begin
	match d1e0.dexp1_node with
	  | DE1lam_sta_ana (arg, d1e_body) -> begin
	      let arg = sarg1_list_tr arg in
	      let s2vvs = sarg2_list_rbind loc arg s2vs in
	      let sub = List.map
                 (function (s2v, s2v') -> (s2v, sexp2_var s2v')) s2vvs in
              let s2vs = List.map (function (s2v, s2v') -> s2v') s2vvs in
	      let () = SEnv2.SEXP2env.push () in
	      let () = SEnv2.sexp2_env_add_var_list s2vs in
              let s2ps = sexp2_list_subst sub s2ps in
              let s2e = sexp2_subst sub s2e in
	      let d2e_body = dexp1_tr_dn d1e_body s2e in
	      let () = SEnv2.SEXP2env.pop () in
		dexp2_lam_sta loc s2vs s2ps d2e_body
	    end
	  | _ -> dexp2_lam_sta loc s2vs s2ps (dexp1_tr_dn d1e0 s2e)
      end
    | SE2clo (knd, s2e_fun) -> begin
	let fc = Syn.FUNCLOclo knd in dexp1_tr_dn_fun loc fc d1e0 s2e_fun
      end
    | SE2fun _ -> dexp1_tr_dn_fun loc (Syn.FUNCLOfun) d1e0 s2e0
    | _ -> dexp2_ann_type loc (dexp1_tr d1e0) s2e0
(* end of [dexp1_tr_dn] *)

and dexp1_tr_dn_fun loc
  (fc: Syn.funclo) (d1e0: dexp1) (s2e_fun: sexp2): dexp2 = begin
  match s2e_fun.sexp2_node with
    | SE2fun (lin, sf2e, (npf1, s2es_arg), s2e_res) -> begin
	match d1e0.dexp1_node with
	  | DE1lam_dyn (is_lin, p1t, d1e_body) -> begin (* is_lin = false *)
	      let p2t = pat1_arg_tr p1t in
	      let (npf2, p2ts) = match p2t.pat2_node with
		| PT2list np2ts -> np2ts | _ -> (0, [p2t]) in
	      let () =
		if npf1 <> npf2 then
		  dexp1_tr_dn_errmsg_lam_dyn_pfarg p2t.pat2_loc in
	      let () =
		let n1 = List.length s2es_arg and n2 = List.length p2ts in
		  match compare n1 n2 with
		    | 0 -> ()
		    | i -> dexp1_tr_dn_errmsg_lam_dyn_arg p2t.pat2_loc i in
	      let p2ts = List.map2
                 (fun p2t s2e -> pat2_ann p2t.pat2_loc p2t s2e) p2ts s2es_arg in
	      let () = SDEnv2.stadynenv2_push () in
	      let () = SEnv2.sexp2_env_add_var_list p2t.pat2_svs in
	      let () = SDEnv2.dexp2_env_add_var_list p2t.pat2_dvs in
	      let d2e_body = dexp1_tr_dn d1e_body s2e_res in
	      let () = SDEnv2.stadynenv2_pop () in
	      let d2e_body = dexp2_ann_seff d2e_body.dexp2_loc d2e_body sf2e in
	      let d2e_body = dexp2_ann_funclo d2e_body.dexp2_loc d2e_body fc in
		dexp2_lam_dyn loc is_lin (npf1, p2ts) d2e_body
	    end
	  | _ -> dexp2_ann_type loc (dexp1_tr d1e0) s2e_fun
      end
    | _ -> begin
	PR.eprintf "%a: dexp1_tr_dn_fun: s2e_fun = %a\n"
	  Loc.fprint loc fprint_sexp2 s2e_fun;
	Err.abort ()
      end
end (* end of [dexp1_tr_dn_fun] *)

(* ****** ****** *)

and mid1_list_tr (m1ids: moditemdec1 list): moditemdec2 list =
  let rec aux res = function
    | m1id :: m1ids -> begin match m1id.moditemdec1_node with
	| MID1sexpdefs (os1t, xs) ->
	    let () = dec1_sexpdef_list_tr false (srt1_opt_tr os1t) xs in
	      aux res m1ids

	| MID1typedefrecs xs ->
	    let () = dec1_sexpdef_list_tr true (Some srt2_type) xs in
	      aux res m1ids

	| MID1funs (fk, starg, xs) ->
	    let s2tvs = List.map srt2_var_make starg in
	    let () = SEnv2.SRT2env.push () in
	    let () = SEnv2.srt2_env_add_var_list s2tvs in
	    let xs = dec1_fun_list_tr fk s2tvs [] xs in
	    let () = SEnv2.SRT2env.pop () in
	    let d2 = moditemdec2_funs m1id.moditemdec1_loc fk xs in
	      aux (d2 :: res) m1ids

	| MID1vals (vk, xs) ->
	    let xs = dec1_val_list_tr false (* is_recursive *) xs in
	    let d2 = moditemdec2_vals m1id.moditemdec1_loc vk xs in
	      aux (d2 :: res) m1ids

	| MID1valrecs xs ->
	    let xs = dec1_val_list_tr true (* is_recursive *) xs in
	    let d2 = moditemdec2_valrecs m1id.moditemdec1_loc xs in
	      aux (d2 :: res) m1ids
      end
    | [] -> List.rev res in
    aux [] m1ids
(* end of [mid1_list_tr] *)

(* ****** ****** *)

and sexparg1_tr (s1a: sexparg1): sexparg2 =
  match s1a with
    | SEXPARG1one -> SEXPARG2one
    | SEXPARG1all -> SEXPARG2all
    | SEXPARG1seq s1es -> SEXPARG2seq (sexp1_list_tr_up s1es)

(* ****** ****** *)

and cla1_tr (n: int) (c1l: cla1): cla2 =
  let p2ts = pat1_list_tr c1l.cla1_pat in
(*
  let () =
    PR.fprintf stdout "cla1_tr: p2ts = %a\n" fprint_pat2_list p2ts in
*)
  let () =
    let n' = List.length p2ts in
      if n' < n then cla1_tr_errmsg_1 c1l
      else if n' > n then cla1_tr_errmsg_2 c1l
      else () in
  let () = SDEnv2.stadynenv2_push () in
  let () =
    List.iter
      (function p2t -> begin
	 SEnv2.sexp2_env_add_var_list p2t.pat2_svs;
	 SDEnv2.dexp2_env_add_var_list p2t.pat2_dvs
       end)
      p2ts in
  let gua = dexp1_opt_tr (c1l.cla1_gua) in
  let d2e = dexp1_tr (c1l.cla1_body) in
  let () = SDEnv2.stadynenv2_pop () in
    cla2 c1l.cla1_loc p2ts gua c1l.cla1_isseq c1l.cla1_isneg d2e
(* end of [cla1_tr] *)

and cla1_list_tr (n: int) (c1ls: cla1 list): cla2 list =
  List.map (cla1_tr n) c1ls

(* ****** ****** *)

and statype1_tr loc0 (sty1: statype1): statype2 =
  let (sty1_qua, sty1_bd) = sty1 in
  let () = SEnv2.SEXP2env.push () in
  let (sty1_s2vs, sty1_s2ps) = squas1_tr sty1_qua in
  let sty1_bd = statype1_body_tr loc0 sty1_bd in
  let () = SEnv2.SEXP2env.pop () in
    statype2_make sty1_s2vs sty1_s2ps None sty1_bd
(* end of [statype1_tr] *)

and statype1_opt_tr loc0 (osty1: statype1 option): statype2 option =
  match osty1 with None -> None | Some sty1 -> Some (statype1_tr loc0 sty1) 

and statype1_body_tr loc0 (sty1_bd: statype1_body): statype2_body =
  let aux (id, os1e) =
    let d2v = match dexp2_env_find id with
      | Some (DI2var d2v) -> d2v
      | _ -> loopinv1_tr_errmsg_1 id in
    let s2t =
      if dvar2_is_mutable d2v then srt2_viewt0ype else srt2_view in
    let os2e = match os1e with
      | Some s1e -> Some (sexp1_tr_dn s1e s2t)
      | None -> None in
      (d2v, os2e) in
    List.map aux sty1_bd
(* end of [statype1_body_tr] *)

and loopinv1_tr (inv1: loopinv1): loopinv2 =
  let loc = inv1.loopinv1_loc in
  let (s2vs, s2ps) = squas1_tr inv1.loopinv1_qua in
  let met = match inv1.loopinv1_met with
    | Some s1is -> Some (List.map sexp1_tr_dn_int s1is)
    | None -> None in
  let arg = statype1_body_tr loc inv1.loopinv1_arg in
  let res = statype1_opt_tr loc inv1.loopinv1_res in
    loopinv2_make loc s2vs s2ps met arg res
(* end of [loopinv1_tr] *)

and loopinv1_opt_tr (oinv1: loopinv1 option): loopinv2 option =
  match oinv1 with None -> None | Some inv1 -> Some (loopinv1_tr inv1)

(* ****** ****** *)

and dec1_symintr_tr (loc: loc) (ids: Syn.did list): unit =
  let aux id =
    let s = Syn.sym_of_did id in SDEnv2.DEXP2env.add s (DI2sym []) in
    List.iter aux ids
(* end of [dec1_symintr_tr] *)

and dec1_symintr_tr_if (loc: loc) (ids: Syn.did list): unit =
  if staload_level_get () > 0 then overload_list_add_symintr loc ids
  else dec1_symintr_tr loc ids

and dec1_symelim_tr (loc: loc) (ids: Syn.did list): unit =
  let aux id =
    let s = Syn.sym_of_did id in
      match dexp2_env_find_sym s with
	| Some (DI2sym d2is) ->  SDEnv2.DEXP2env.add s (DI2sym [])
	| _ -> dec1_symelim_errmsg loc id in
    List.iter aux ids
(* end of [dec1_symelim_tr] *)

and dec1_symelim_tr_if (loc: loc) (ids: Syn.did list): unit =
  if staload_level_get () > 0 then overload_list_add_symelim loc ids
  else dec1_symelim_tr loc ids

(* ****** ****** *)

and dec1_srtdef_tr (d: dec1_srtdef): unit =
  SEnv2.SRT2env.add
    (Syn.sym_of_srt_id d.dec1_srtdef_name)
    (srtext1_tr d.dec1_srtdef_def) 

and dec1_srtdef_list_tr (ds: dec1_srtdef list): unit =
  List.iter dec1_srtdef_tr ds

and dec1_datsrt_tr
  (arg: srt2_var list) (res: srt2) (d: dec1_datsrt): scst2 list =
  let aux (d1c: datsrtcon1): scst2 =
    let name = d1c.datsrtcon1_name in
    let arg = srt1_list_tr d1c.datsrtcon1_arg in
    let s2t = srt2_fun arg res in
    let s2c =
      scst2_make name
	s2t (* sort *)
	None (* is_abstract *)
	true (* is_constructor *)
	false (* is_recursive *)
	None (* argument *) 
	None (* is_listlike *)
	[] (* environment *)
	None (* definition *)
        false (* is assumed? *) in
      (sexp2_env_add_cst s2c; s2c) in
  let () = SEnv2.SRT2env.push () in
  let () = SEnv2.srt2_env_add_var_list arg in
  let s2cs = List.map aux (d.dec1_datsrt_con) in
  let () = SEnv2.SRT2env.pop () in
    s2cs
(* end of [dec1_datsrt_tr] *)

and dec1_datsrt_list_tr (ds: dec1_datsrt list): unit =
  let rec aux1 = function (* static term constructors *)
    | (sd2t, d) :: rest ->
	let s2t = SRT2bas (SRT2BASdef sd2t) in
	let eq =
	  scst2_make Syn.sid_equal
	    (srt2_fun [s2t; s2t] srt2_bool) (* sort *)
	    None (* is_abstract *)
	    false (* is_constructor *)
	    false (* is_recursive *)
            None (* argument *)
	    None (* is_listlike *)
	    [] (* environment *)
	    None (* definition *)
            false (* is_defined *) in
	let () = sexp2_env_add_cst eq in
	let s2cs = dec1_datsrt_tr (sd2t.srt2_dat_arg) s2t d in
	  (sd2t.srt2_dat_con <- s2cs; aux1 rest)
    | [] -> () in
  let rec aux2 (res: (srt2_dat * dec1_datsrt) list) =
    function (* sort constructors *)
      | d :: ds ->
	  let name = d.dec1_datsrt_name in
	  let arg = List.map srt2_var_make d.dec1_datsrt_arg in
	  let sd2t = srt2_dat_make name arg in
	  let s2t = SRT2bas (SRT2BASdef sd2t) in
	  let s2te = STE2srt s2t in
	  let () = SEnv2.SRT2env.add (Syn.sym_of_srt_id name) s2te in
	    aux2 ((sd2t, d) :: res) ds
      | [] -> aux1 res in
    aux2 [] ds
(* end of [dec1_datsrt_tr] *)

(* ****** ****** *)

and dec1_stacon_tr (s2t_res: srt2) (d: dec1_stacon): unit =
  let name = d.dec1_stacon_name in
  let arg_opt = match d.dec1_stacon_arg with
    | Some arg -> Some
	(List.map (function (id_opt, s1t, i) -> (id_opt, srt1_tr s1t, i)) arg)
    | None -> None in
  let s2t_fun = match arg_opt with
    | Some arg ->
	let s2ts_arg = List.map (function (_, s2t, _) -> s2t) arg in
	  srt2_fun s2ts_arg s2t_res
    | None -> s2t_res in
  let () = SEnv2.SEXP2env.push () in
  let s2vs_opt =
    let aux (oid, s2t, _): svar2 =
      let s2v = match oid with
	| Some id -> svar2_new_with_id id s2t | None -> svar2_new s2t in
	(SEnv2.sexp2_env_add_var s2v; s2v) in
      match arg_opt with
	| Some arg -> Some (List.map aux arg) | None -> None in
  let def = match d.dec1_stacon_def with
    | Some s1e -> begin
	let s2e_body = sexp1_tr_dn s1e s2t_res in
	let s2e_def =
	  match s2vs_opt with
	    | Some s2vs -> sexp2_lam_with_sort s2t_fun s2vs s2e_body
	    | None -> s2e_body in
	  Some s2e_def
      end
    | None -> None in
  let () = SEnv2.SEXP2env.pop () in
  let s2c =
    scst2_make
      name
      s2t_fun (* sort *)
      (Some def) (* is_abstract *)
      true (* is_constructor *)
      false (* is_recursive *)
      arg_opt (* argument *)
      None (* is_listlike *)
      [] (* environment *)
      None (* definition *)
      false (* is assumed? *) in
    sexp2_env_add_cst s2c
(* end of [dec1_stacon_tr] *)

and dec1_stacon_list_tr (s2t: srt2) (ds: dec1_stacon list): unit =
  List.iter (dec1_stacon_tr s2t) ds

(* ****** ****** *)

and dec1_stacst_tr (d: dec1_stacst): unit =
  let name = d.dec1_stacst_name in
  let arg = List.map srt1_list_tr d.dec1_stacst_arg in
  let s2t =
    let rec aux s2t = function
      | s2ts :: s2tss -> aux (srt2_fun s2ts s2t) s2tss
      | [] -> s2t in
      aux (srt1_tr d.dec1_stacst_sort) (List.rev arg) in
  let s2c =
    scst2_make
      name (* name *)
      s2t (* sort *)
      None (* is_abstract *)
      false (* is_constructor *)
      false (* is_recursive *)
      None (* argument *)
      None (* is_listlike *)
      [] (* environment *)
      None (* definition *)
      false (* is assumed? *) in
    sexp2_env_add_cst s2c
(* end of [dec1_stacst_tr] *)

and dec1_stacst_list_tr (ds: dec1_stacst list): unit =
  List.iter dec1_stacst_tr ds

(* ****** ****** *)

and dec1_stavar_tr (d: dec1_stavar): dec2_stavar =
  let s2t = srt1_tr d.dec1_stavar_sort in
  let s2v = svar2_new_with_id (d.dec1_stavar_name) s2t in
  let () = SEnv2.sexp2_env_add_var s2v in
    dec2_stavar (d.dec1_stavar_loc) s2v
(* end of [dec1_stavar_tr] *)

and dec1_stavar_list_tr (ds: dec1_stavar list): dec2_stavar list =
  List.map dec1_stavar_tr ds

(* ****** ****** *)

and dec1_sexpdef_sasp_tr_aux
  (loc: loc) (args: (sarg1 list) list)
  (res: srt2 option) (body: sexp1): sexp2 =
  let aux1 ((id, os1t): sarg1): svar2 =
    let s2v = match os1t with
      | Some s1t -> svar2_new_with_id id (srt1_tr s1t)
      | None -> dec1_sexpdef_sasp_tr_aux_errmsg_1 loc id in
    let () = SEnv2.sexp2_env_add_var s2v in s2v in
  let () = SEnv2.SEXP2env.push () in
  let args =  List.map (List.map aux1) args in
  let body = match res with
    | Some s2t -> sexp1_tr_dn body s2t | None -> sexp1_tr_up body in
  let () = SEnv2.SEXP2env.pop () in
  let rec aux3 (body: sexp2) = function
    | arg :: args ->
	let s2ts = List.map (function s2v -> s2v.svar2_sort) arg in
	let s2t = srt2_fun s2ts (body.sexp2_sort) in
	  aux3 (sexp2_lam_with_sort s2t arg body) args
    | [] -> body in
    aux3 body (List.rev args)
(* end of [dec1_sexpdef_sasp_tr_aux] *)

and dec1_sexpdef_tr_rec (s2c: scst2) (d: dec1_sexpdef): unit =
  let loc = d.dec1_sexpdef_loc in
  let s2e =
    let arg = d.dec1_sexpdef_arg in
    let def = d.dec1_sexpdef_def in
      dec1_sexpdef_sasp_tr_aux loc arg None def in
  let () =
    let s2t_s2e = s2e.sexp2_sort in
    let s2t_s2c = s2c.scst2_sort in
      if not (srt2_leq s2t_s2e s2t_s2c) then
	dec1_sexpdef_tr_rec_errmsg_1 loc in
  let () = s2c.scst2_def <- Some s2e in
  let fvs = sexp2_fvs_0 s2e in
  let env = sexp2_list_of_stamps fvs in
  let () = s2c.scst2_env <- env in ()
(* end of [dec1_sexpdef_tr_rec] *)

and dec1_sexpdef_tr_norec
  (os2t0_res: srt2 option) (d: dec1_sexpdef): scst2 =
  let loc = d.dec1_sexpdef_loc in
  let os1t_res = d.dec1_sexpdef_res in
  let os2t_res = match os1t_res with
    | Some s1t -> begin
	let s2t = srt1_tr s1t in match os2t0_res with
	  | Some s2t0 ->
	      if srt2_leq s2t s2t0 then os2t0_res else
		dec1_sexpdef_tr_norec_errmsg_1 loc
	  | None -> Some s2t
      end
    | None -> os2t0_res in
  let s2e =
    let arg = d.dec1_sexpdef_arg in
    let def = d.dec1_sexpdef_def in
      dec1_sexpdef_sasp_tr_aux loc arg os2t_res def in
  let s2c =
    scst2_make
      d.dec1_sexpdef_name (* name *)
      s2e.sexp2_sort (* sort *)
      None (* is_abstract *)
      false (* is_constructor *)
      false (* is_recursive *)
      None (* argument *)
      None (* is_listlike *)
      [] (* environment *)
      (Some s2e) (* definition *)
      true (* is assumed? *) in
  let fvs = sexp2_fvs_0 s2e in
  let env = sexp2_list_of_stamps fvs in
  let () = s2c.scst2_env <- env in s2c
(* end [dec1_sexpdef_tr_norec] *)

and srt2_args_res (args: (sarg1 list) list) (res: srt2 option): srt2 option =
  let rec aux1 (s2ts: srt2 list) = function
    | (_, os1t) :: arg -> begin match os1t with
	| Some s1t ->
	    let s2t = srt1_tr s1t in aux1 (s2t :: s2ts) arg
	| None -> None
      end
    | [] -> Some (List.rev s2ts) in
  let rec aux2 (s2tss: srt2 list list) = function
    | arg :: args -> begin
	let os2ts = aux1 [] arg in
	  match os2ts with
	    | Some s2ts -> aux2 (s2ts :: s2tss) args
	    | None -> None
      end
    | [] -> Some s2tss in
  let rec aux3 (res: srt2) = function
    | s2ts :: s2tss -> aux3 (srt2_fun s2ts res) s2tss
    | [] -> res in

    match res with
      | Some s2t -> begin
	  let os2tss = aux2 [] args in match os2tss with
	    | Some s2tss -> Some (aux3 s2t s2tss) | None -> None
	end
      | None -> None
(* end of [srt2_args_res] *)

and dec1_sexpdef_list_tr_rec
  (os2t0_res: srt2 option) (ds: dec1_sexpdef list): unit =
  let rec aux s2cs ds = match ds with
    | d :: ds -> begin
	let loc = d.dec1_sexpdef_loc in
	let os1t_res = d.dec1_sexpdef_res in
	let os2t_res = match os1t_res with
	  | Some s1t -> begin
	      let s2t = srt1_tr s1t in match os2t0_res with
		| Some s2t0 ->
		    if srt2_leq s2t s2t0 then os2t0_res else
		      dec1_sexpdef_list_tr_rec_errmsg_1 loc
		| None -> Some s2t
	    end
	  | None -> os2t0_res in
	let os2t =
	  srt2_args_res (d.dec1_sexpdef_arg) os2t_res in
	  match os2t with
	    | Some s2t -> begin
		let s2c =
		  scst2_make
		    d.dec1_sexpdef_name (* name *)
		    s2t (* sort *)
		    None (* is_abstract *)
		    false (* is_constructor *)
		    true (* is_recursive *)
		    None (* argument *)
		    None (* is_listlike *)
		    [] (* environment *)
		    None (* definition *)
                    false (* is assumed? *) in
		let () = sexp2_env_add_cst s2c in
		  aux (s2c :: s2cs) ds
	      end
	    | None -> dec1_sexpdef_list_tr_rec_errmsg_2 loc
      end
    | [] -> List.rev s2cs in
  let s2cs = aux [] ds in List.iter2 dec1_sexpdef_tr_rec s2cs ds
(* end of [dec1_sexpdef_list_tr_rec] *)

and dec1_sexpdef_list_tr_norec (os2t: srt2 option) (ds: dec1_sexpdef list): unit =
  let s2cs = List.map (function d -> dec1_sexpdef_tr_norec os2t d) ds in
    List.iter sexp2_env_add_cst s2cs

and dec1_sexpdef_list_tr (is_recursive: bool)
  (os2t: srt2 option) (ds: dec1_sexpdef list): unit =
  if is_recursive then dec1_sexpdef_list_tr_rec os2t ds
  else dec1_sexpdef_list_tr_norec os2t ds

and dec1_sasp_tr (d: dec1_sasp): dec2_sasp =
  let loc = d.dec1_sasp_loc in
  let qid = d.dec1_sasp_name in
    match sexp2_env_oqfind qid with
      | Some (SI2cst s2cs) -> begin match s2cs with
	  | [s2c] -> begin
	      if scst2_is_abstract s2c then begin
		let res = srt1_opt_tr d.dec1_sasp_res in
		let s2e =
		  dec1_sexpdef_sasp_tr_aux loc
		    d.dec1_sasp_arg res d.dec1_sasp_def in
		let s2t_s2e = s2e.sexp2_sort in
		let s2t_s2c = s2c.scst2_sort in
		  if srt2_leq s2t_s2e s2t_s2c then dec2_sasp loc s2c s2e
		  else dec1_sasp_tr_errmsg_1 loc qid
	      end else begin
		dec1_sasp_tr_errmsg_2 loc qid
	      end
	    end
	  | _ -> dec1_sasp_tr_errmsg_3 loc qid
	end
      | _ -> dec1_sasp_tr_errmsg_4 loc qid
(* end of [dec1_sasp] *)

and dec1_sasp_list_tr (ds: dec1_sasp list): dec2_sasp list =
  List.map dec1_sasp_tr ds

(* ****** ****** *)

and dec1_dyncst_tr (dck: Syn.dcstkind)
  (decarg: (svar2 list * sexp2 list) list) (d: dec1_dyncst): dcst2 =
  let loc = d.dec1_dyncst_loc in
  let name = d.dec1_dyncst_name in
  let filename = d.dec1_dyncst_filename in
  let s2e =
    if Syn.dcstkind_is_proof dck then sexp1_tr_dn_view d.dec1_dyncst_sexp
    else sexp1_tr_dn_viewt0ype d.dec1_dyncst_sexp in
  let arity = sexp2_arity s2e in
  let extdef = d.dec1_dyncst_extdef in
  let d2c = dcst2_make loc name filename dck decarg arity s2e extdef in
(*
  let () =
    PR.fprintf stdout "dec1_dyncst_tr: d2c = %a\n" fprint_dcst2 d2c in
  let () =
    PR.fprintf stdout "dec1_dyncst_tr: decarg = %a\n" fprint_decarg2 decarg in
*)
  let () = SDEnv2.dexp2_env_add_cst d2c in d2c
(* end of [dec1_dyncst_tr] *)

and dec1_dyncst_list_tr (dck: Syn.dcstkind)
  (decarg: (svar2 list * sexp2 list) list) (ds: dec1_dyncst list)
  : dcst2 list = List.map (dec1_dyncst_tr dck decarg) ds

(* ****** ****** *)

and datcon1_tr (filename: Fil.filename) (vwtp: bool)
  (s2c: scst2) (s2vs0: svar2 list) (d1c: datcon1): dcon2 =
  let loc = d1c.datcon1_loc in
  let name = d1c.datcon1_name in
  let () = SEnv2.SEXP2env.push () in
  let () = SEnv2.sexp2_env_add_var_list s2vs0 in
  let qua = 
    let qua = squas1_list_tr (d1c.datcon1_qua) in 
      match s2vs0 with
	| _ :: _ -> (s2vs0, []) :: qua
	| [] -> qua in
  let (os2ts_s2c_ind, s2t_s2c) = match s2c.scst2_sort with
    | SRT2fun (s2ts, s2t) -> (Some s2ts, s2t) | s2t -> (None, s2t) in
  let (npf, s1es_arg) = d1c.datcon1_arg in
  let s2es_arg =
    let s2t_pfarg: srt2 =
      if srt2_is_linear s2t_s2c then srt2_view else srt2_prop in
    let s2t_arg: srt2 =
      if srt2_is_proof s2t_s2c then s2t_pfarg else
	if srt2_is_linear s2t_s2c then srt2_viewt0ype else srt2_t0ype in
    let rec aux i = function
      | s1e :: s1es -> begin
	  let s2t = if i < npf then s2t_pfarg else s2t_arg in
	    sexp1_tr_dn s1e s2t :: aux (i+1) s1es
	end
      | [] -> [] in
      aux 0 s1es_arg in
  let s2es_ind = match d1c.datcon1_ind, os2ts_s2c_ind with
    | Some s1es, Some s2ts ->
	let n1 = List.length s1es in
	let n2 = List.length s2ts in
	  if n1 > n2 then dec1_dat_tr_errmsg_1 loc name
	  else if n1 < n2 then dec1_dat_tr_errmsg_2 loc name
	  else Some (sexp1_list_tr_dn loc s1es s2ts)
    | None, None -> None
    | Some _, None -> dec1_dat_tr_errmsg_3 loc name
    | None, Some _ -> dec1_dat_tr_errmsg_4 loc name in
  let () = SEnv2.SEXP2env.pop () in
  let d2c = dcon2_make loc
    s2c name filename vwtp qua (npf, s2es_arg) s2es_ind in
  let () = SDEnv2.dexp2_env_add_con d2c in
  let () = if vwtp then SEnv2.sexp2_env_add_datcon d2c in
    d2c
(* end of [datcon1_tr] *)

and dec1_dat_tr ((s2c, s2vs0): scst2 * svar2 list) (d: dec1_dat): unit =
  let d2cs =
    let vwtp = srt2_is_viewtype_fun s2c.scst2_sort in
    let f = datcon1_tr d.dec1_dat_filename vwtp s2c s2vs0 in
      List.map f d.dec1_dat_con in
  let () = (* assigning tags to dynamic constructors *)
    let rec aux (i: int) = function
      | d2c :: d2cs -> (d2c.dcon2_tag <- i; aux (i+1) d2cs)
      | [] -> () in
      aux 0 d2cs in
  let is_listlike = match d2cs with
    | [d2c1; d2c2] ->
	if d2c1.dcon2_arity_real == 0 then begin
	  if d2c2.dcon2_arity_real > 0 then Some (d2c1, d2c2)
	  else None
	end else begin
	  if d2c2.dcon2_arity_real == 0 then Some (d2c2, d2c1)
	  else None
	end
    | _ -> None in
  let fvs = dcon2_list_fvs d2cs in
  let s2es = sexp2_list_of_stamps fvs in
    begin
      s2c.scst2_islst <- is_listlike;
      s2c.scst2_cons <- Some d2cs;
      s2c.scst2_env <- s2es;
    end
(* end of [dec1_dat_tr] *)

and dec1_dat_list_tr
  (dtk: Syn.datakind) (s2tvs: srt2_var list)
  (ds1: dec1_dat list) (ds2: dec1_sexpdef list): scst2 list =
  let s2t_res = srt2_datakind dtk in
  let () = SEnv2.SRT2env.push () in
  let () = SEnv2.srt2_env_add_var_list s2tvs in
  let s2c_s2vs_list: (scst2 * svar2 list) list =
    let aux (d: dec1_dat): scst2 * svar2 list =
      let arg = match d.dec1_dat_arg with
	| Some arg -> Some
	    (List.map (function (oid, s1t, i) -> (oid, srt1_tr s1t, i)) arg)
	| None -> None in
      let s2vs =
	let rec aux = function
	  | (oid, s2t, i) :: rest -> begin match oid with
	      | Some id -> (svar2_new_with_id id s2t) :: aux rest
	      | None -> aux rest
	    end
	  | [] -> [] in
	  match arg with Some arg -> aux arg | None -> [] in
      let os2ts_arg = match arg with
	| Some arg -> Some (List.map (function (_, s2t, _) -> s2t) arg)
	| None -> None in
      let s2c = dat_scst2_make (d.dec1_dat_name) os2ts_arg s2t_res arg in
      (sexp2_env_add_cst s2c; (s2c, s2vs)) in
    List.map aux ds1 in
  let () = 
    let f d = sexp2_env_add_cst (dec1_sexpdef_tr_norec None d) in
      List.iter f ds2 in
  let () = List.iter2 dec1_dat_tr s2c_s2vs_list ds1 in
  let () = SEnv2.SRT2env.pop () in
    List.map (function (s2c, _) -> s2c) s2c_s2vs_list
(* end of [dec1_dat_list_tr] *)

(* ****** ****** *)

(* [exn] is considered a viewtype constructor *)
and dec1_exn_tr (s2c: scst2) (d: dec1_exn): dcon2 =
  let loc = d.dec1_exn_loc in
  let name = d.dec1_exn_name in
  let filename = d.dec1_exn_filename in
  let () = SEnv2.SEXP2env.push () in
  let qua = squas1_list_tr (d.dec1_exn_qua) in
  let (npf, s1es_arg) = d.dec1_exn_arg in
  let s2es_arg = List.map sexp1_tr_dn_impredicative s1es_arg in
  let () = SEnv2.SEXP2env.pop () in
  let d2c = dcon2_make loc
    s2c name filename true (*vwtp*) qua (npf, s2es_arg) None in
  let () = d2c.dcon2_tag <- -1 in
  let () = SDEnv2.dexp2_env_add_con d2c in d2c
(* end of [dec1_exn_tr] *)

and dec1_exn_list_tr (ds: dec1_exn list): dcon2 list =
  let s2c = Exception_viewtype.make_cst () in
  let d2cs = List.map (dec1_exn_tr s2c) ds in
  let d2cs0 = match s2c.scst2_cons with
    | Some d2cs0 -> List.rev_append d2cs d2cs0
    | None -> d2cs in
  let () = s2c.scst2_cons <- Some d2cs0 in d2cs
(* end of [dec1_exn_list_tr] *)

(* ****** ****** *)

and dec1_modtype_tr (is_prop: bool) (d: dec1_modtype): unit =
  let rec aux res1 res2 = function
    | mtdi :: mtdis -> begin
	match mtdi.mtitemdec1_node with
	  | MTID1sta (name, s1t) ->
	      let s2t = srt1_tr s1t in
	      let l = Lab.make_with_symbol (Syn.sym_of_sid name) in
	      let s2v = svar2_new_with_id name s2t in
	      let () = SEnv2.sexp2_env_add_var s2v in
		aux ((l, s2v) :: res1) res2 mtdis
	  | MTID1val (is_prop, name, s1e) ->
	      let l = Lab.make_with_symbol (Syn.sym_of_did name) in
	      let s2t = if is_prop then srt2_prop else srt2_type in
	      let s2e = sexp1_tr_dn s1e s2t in
	      	aux res1 ((l, s2e) :: res2) mtdis
	  | MTID1sexpdefs ds ->
	      let () = dec1_sexpdef_list_tr false None ds in
		aux res1 res2 mtdis
	  | MTID1typedefs ds ->
	      let () = dec1_sexpdef_list_tr false (Some srt2_type) ds in
		aux res1 res2 mtdis
	  | MTID1typedefrecs ds ->
	      let () = dec1_sexpdef_list_tr true (Some srt2_type) ds in
		aux res1 res2 mtdis
      end
    | [] -> begin
	let s2t = if is_prop then srt2_prop else srt2_type in
	let res1 = List.rev res1 in
	let res2 = Lab.labeled_list_sort res2 in
	let s2e = sexp2_tyrec_with_sort s2t TYRECbox 0 (*npf*) res2 in
	  (res1, s2e)
      end in
  let () = SEnv2.SEXP2env.push () in
  let (ls2vs, s2e) = aux [] [] (d.dec1_modtype_def) in
  let () = SEnv2.SEXP2env.pop () in
    SEnv2.sexp2_env_add_mod (d.dec1_modtype_name) ls2vs s2e
(* end of [dec1_modtype_tr] *)

and dec1_modtype_list_tr (is_prop: bool) (ds: dec1_modtype list): unit =
  List.iter (dec1_modtype_tr is_prop) ds

(* ****** ****** *)

and dec1_overload_tr
  (loc: loc) (name: Syn.did) (d2i: ditem2): unit =
  let s = Syn.sym_of_did name in
(*
  let () =
    PR.fprintf stdout "dec1_overload_tr: name = %a\n" Syn.fprint_did name in
*)
  let d2is = match dexp2_env_find_sym s with
    | Some (DI2sym d2is) -> d2is
    | _ -> dec1_overload_tr_errmsg_sym loc name in
  let d2is = ditem2_list_overload_extend d2is d2i in
(*
  let () =
    PR.fprintf stdout "dec1_overload_tr: d2is = %a\n" fprint_ditem2_list d2is in
*)
    SDEnv2.DEXP2env.add s (DI2sym d2is)
(* end of [dec1_overload_tr] *)

and dec1_overload_tr_if
  (loc: loc) (name: Syn.did) (qid: Syn.dqual_opt_id): unit =
  let d2i = match dexp2_env_oqfind qid with
    | Some d2i -> d2i | None -> dec1_overload_tr_errmsg_qid loc qid in
    if staload_level_get () > 0 then overload_list_add_bind loc name d2i
    else dec1_overload_tr loc name d2i
(* end of [dec1_overload_tr_if] *)

and dec1_overload_tr_staload (): unit =
  let aux (x: overloaditem): unit = match x with
    | OLIsymintr (loc, ids) -> dec1_symintr_tr loc ids
    | OLIsymelim (loc, ids) -> dec1_symelim_tr loc ids
    | OLIbind (loc, name, d2i) -> dec1_overload_tr loc name d2i in
  if staload_level_get () == 0 then begin
    let xs = overload_list_get () in (overload_list_reset (); List.iter aux xs)
  end (* end of [if] *)
(* end of [dec1_overload_tr_staload] *)

(* ****** ****** *)

and dec1_macdef_tr (is_abbrev: bool) (d: dec1_macdef): unit =
  let loc = d.dec1_macdef_loc in
  let name = d.dec1_macdef_name in
  let () = SDEnv2.DEXP2env.push () in
  let arg =
    let aux_var (x: Syn.did): dvar2 =
      let d2v = dvar2_new_with_id loc x false in
      let () = SDEnv2.dexp2_env_add_var d2v in d2v in
    let aux_var_list (xs: Syn.did list): dvar2 list =
      List.map aux_var xs in
      List.map aux_var_list (d.dec1_macdef_arg) in
  let d2e = dexp1_tr (d.dec1_macdef_def) in
  let () = SDEnv2.DEXP2env.pop () in
  let d2m = dmac2_make loc name is_abbrev arg d2e in
    SDEnv2.dexp2_env_add_mac d2m
(* end of [dec1_macdef_tr] *)

and dec1_macdef_list_tr (is_abbrev: bool) (ds: dec1_macdef list): unit =
  List.iter (dec1_macdef_tr is_abbrev) ds

(* ****** ****** *)

and dec1_val_tr (p2t: pat2) (d: dec1_val): dec2_val =
  let d2e = dexp1_tr (d.dec1_val_def) in
    match p2t.pat2_node with
      | PT2ann (p2t, s2e) -> dec2_val d.dec1_val_loc p2t d2e (Some s2e)
      | _ -> dec2_val d.dec1_val_loc p2t d2e None
(* end of [dec1_val_tr] *)

and dec1_val_list_tr (is_recursive: bool) (ds: dec1_val list)
  : dec2_val list =
  let (p2ts, s2vs, d2vs) =
    let rec aux p2ts s2vs d2vs = function
      | d :: ds ->
	  let p1t = d.dec1_val_pat in
	  let loc = p1t.pat1_loc in
	  let p2t = pat1_tr p1t in
	  let s2vs = svar2_linear_add_list loc s2vs p2t.pat2_svs in
	  let d2vs = dvar2_linear_add_list loc d2vs p2t.pat2_dvs in
	    aux (p2t :: p2ts) s2vs d2vs ds
      | [] -> (List.rev p2ts, s2vs, d2vs) in
      aux [] [] [] ds in
    if is_recursive then
      let () = SDEnv2.dexp2_env_add_var_list d2vs in
      let ds2 = List.map2 dec1_val_tr p2ts ds in
      let () = SEnv2.sexp2_env_add_var_list s2vs in ds2
    else
      let ds2 = List.map2 dec1_val_tr p2ts ds in
      let () = SDEnv2.dexp2_env_add_var_list d2vs in
      let () = SEnv2.sexp2_env_add_var_list s2vs in ds2
(* end of [dec1_val_list_tr] *)

(* ****** ****** *)

and dec1_fun_tr
  (d2v: dvar2) (decarg: decarg2) (d: dec1_fun): dec2_fun =
  let () = d2v.dvar2_decarg <- decarg in
  let d2e = dexp1_tr d.dec1_fun_def in
  let os2e = sexp1_opt_tr_up d.dec1_fun_ann in
  let d2e = match os2e with
    | Some s2e -> dexp2_ann_type d2e.dexp2_loc d2e s2e
    | None -> d2e in
    dec2_fun d.dec1_fun_loc d2v d2e
(* end of [dec1_fun_tr] *)

and dec1_fun_list_tr
  (fk: Syn.funkind) (s2tvs: srt2_var list)
  (decarg: decarg2) (ds: dec1_fun list): dec2_fun list =
  let is_recursive = Syn.funkind_is_recursive fk in
  let d2vs =
    let f d =
      dvar2_new_with_id
	d.dec1_fun_loc d.dec1_fun_name true (*is_fixed*) in
      List.map f ds in
  let ds2 =
    let f d2v d = dec1_fun_tr d2v decarg d in
      if is_recursive then begin
	let () = SDEnv2.dexp2_env_add_var_list d2vs in
	let ds2 = List.map2 f d2vs ds in
	  ds2
      end else begin
	let ds2 = List.map2 f d2vs ds in
	let () = SDEnv2.dexp2_env_add_var_list d2vs in ds2
      end in
    ds2 (* end of [let] *)
(* end of [dec1_fun_list_tr] *)

(* ****** ****** *)

and dec1_var_tr (d: dec1_var): dec2_var =
  let loc = d.dec1_var_loc in
  let name = d.dec1_var_name in
  let d2v_ptr = dvar2_new_with_id loc name false (* is_fixed *) in
  let s2v_ptr = svar2_new_with_id (Syn.sid_of_did name) srt2_addr in
  let () = d2v_ptr.dvar2_addr <- Some (sexp2_var s2v_ptr) in
  let os2e = match d.dec1_var_type with
    | Some s1e -> Some (sexp1_tr_dn_impredicative s1e)
    | None -> None in
    dec2_var loc d2v_ptr s2v_ptr os2e (dexp1_opt_tr d.dec1_var_ini)
(* end of [dec1_var_tr] *)

and dec1_var_list_tr (ds: dec1_var list): dec2_var list =
  let ds2 = List.map dec1_var_tr ds in
  let aux d2 =
    begin
      SEnv2.sexp2_env_add_var d2.dec2_var_svar;
      SDEnv2.dexp2_env_add_var d2.dec2_var_dvar;
    end in
  let () = List.iter aux ds2 in ds2
(* end of [dec1_var_list_tr] *)

(* ****** ****** *)

and dec1_impl_tr
  (decarg: sarg1 list list) (d: dec1_impl): dec2_impl =
  let loc = d.dec1_impl_loc in
(*
  let rec aux1 res s2vpss s2e = match s2vpss with
    | (s2vs, s2ps) :: s2vpss ->
	let (sub, s2vs) = subst_extend [] s2vs in
	let s2ps = sexp2_list_subst sub s2ps in
	let s2e = sexp2_subst sub s2e in
	  aux1 ((s2vs, s2ps) :: res) s2vpss s2e
    | [] -> (List.rev res, s2e) in
*)
  let rec aux2 res args s2vpss s2e = match args with
    | arg :: args -> begin match s2vpss with
	| (s2vs, s2ps) :: s2vpss -> begin
	    let arg = sarg1_list_tr arg in
	    let s2vvs = sarg2_list_rbind loc arg s2vs in
	    let sub = List.map
              (function (s2v, s2v') -> (s2v, sexp2_var s2v')) s2vvs in
	    let s2vs' = List.map (function (s2v, s2v') -> s2v') s2vvs in
	    let () = SEnv2.sexp2_env_add_var_list s2vs' in
	    let s2ps' = sexp2_list_subst sub s2ps in
	    let s2e = sexp2_subst sub s2e in
	      aux2 ((s2vs', s2ps') :: res) args s2vpss s2e
          end (* end of [::] *)
	| [] -> begin
	    PR.fprintf stderr "%a: dec1_impl_tr: aux2: overly applied.\n"
	      Loc.fprint loc;
	    Err.abort ();
	  end (* end of [nil] *)
      end (* end of [::] *)
    | [] -> begin match s2vpss with
      | _ :: _ -> begin
(*
        // aux1 res s2vpss s2e
        // automatic instantiation is not supported as it can readily lead
        // to confusion as for whether an implementation is actually compiled.
*)
        PR.fprintf stderr "%a: dec1_impl_tr: aux2: under applied.\n"
	  Loc.fprint loc;
	Err.abort ();
        end (* end of [::] *)
      | [] -> (List.rev res, s2e)
      end in
  let qid = d.dec1_impl_name in match dexp2_env_oqfind qid with
    | Some (DI2cst d2c) -> begin
	let () = SDEnv2.stadynenv2_push () in
	let (decarg, s2e_d2c) =
          aux2 [] decarg d2c.dcst2_decarg d2c.dcst2_type in
	let tmparg = List.map sexp1_list_tr_up d.dec1_impl_tmparg in
	let () = match tmparg with
	  | _ :: _ -> begin
              PR.fprintf stderr
		"%a: dec1_impl_tr: nonempty tmparg: not yet supported.\n"
		Loc.fprint loc;
	      Err.abort ()
            end (* end of [::] *)
	  | [] -> () in
        let def = dexp1_tr_dn d.dec1_impl_def s2e_d2c in
        let () = SDEnv2.stadynenv2_pop () in
	let () = d2c.dcst2_def <- Some def in
	  dec2_impl d.dec1_impl_loc d2c decarg tmparg def
      end (* end of [Some] *)
    | _ -> dec1_impl_tr_errmsg_qid d.dec1_impl_loc qid
(* end of [dec1_impl_tr] *)

and dec1_impl_list_tr
  (decarg: sarg1 list list) (ds: dec1_impl list): dec2_impl list =
  List.map (dec1_impl_tr decarg) ds

(* ****** ****** *)

and dec1_local_tr (loc: loc) (head1: dec1 list) (body1: dec1 list)
  : dec2 = 
  let () = push_all () in
  let head2 = dec1_list_tr head1 in
  let () = push_all () in
  let body2 = dec1_list_tr body1 in
  let () = localjoin_all () in
    dec2_local loc head2 body2
(* end of [dec1_local_tr] *)

(* ****** ****** *)

and dec1_staload_tr (loc: loc) (osid: Syn.sid option)
  (f: Fil.filename) (is_loaded: bool) (staload_res: trans1_res): dec2 =
  let fullname = Fil.filename_fullname f in
(*
  let () =
    PR.fprintf stdout "dec1_staload_tr: fullname = %s\n" fullname in
*)
  let symname = NS.make_name fullname in
  let ods2 = match NS.stadynenv_find symname with
    | Some _ -> None
    | None ->
        let () = staload_level_inc () in
	let () = save_all () in
	let () = Env1.E0xpEnv.set_top staload_res.trans1_res_defs in
	let ds2 = dec1_list_tr staload_res.trans1_res_decs in
	let (t1, t2, t3) = get_top_all () in
	let () = restore_all () in
        let () = staload_level_dec () in
	let () = dec1_overload_tr_staload () in
	let () = NS.stadynenv_add symname (t1, t2, t3, ds2) in
	  Some ds2 in
  let is_static = staload_res.trans1_res_sta in
  let () = match osid with
    | Some id -> begin
	if is_static then SEnv2.sexp2_env_add_fil id f
      end
    | None -> begin
	if is_static then NS.NameSpace.add symname (* opened file *)
      end in
    dec2_staload loc f ods2
(* end of [dec1_staload_tr] *)

(*

and dec1_dynload_tr (loc: loc)
  (f: Fil.filename) (is_loaded: bool) (dynload_res: trans1_res): dec2 =
  let name = NS.make_name (Fil.filename_fullname f) in
  let ds2 = match NS.stadynenv_find name with
    | Some (_, _, _, ds2) -> ds2
    | None ->
	let () = save_all () in
	let () = Env1.E0xpEnv.set_top dynload_res.trans1_res_defs in
	let ds2 = dec1_list_tr dynload_res.trans1_res_decs in
	let () = restore_all () in
	  ds2 in
    dec2_dynload loc f is_loaded ds2
(* end of [dec1_dynload_tr] *)

*)

(* ****** ****** *)

and dec1_list_tr_aux1 (ds: dec1 list) (res: dec2 list): dec2 list = begin
  match ds with d :: ds -> dec1_list_tr_aux2 d ds res | [] -> List.rev res
end (* end of [dec1_list_tr_aux1] *)

and dec1_list_tr_aux2
  (d: dec1) (ds: dec1 list) (res: dec2 list): dec2 list = begin
  match d.dec1_node with
  | DC1symintr ids ->
      let () = dec1_symintr_tr_if d.dec1_loc ids in
	dec1_list_tr_aux1 ds res
  | DC1symelim ids ->
      let () = dec1_symelim_tr_if d.dec1_loc ids in
	dec1_list_tr_aux1 ds res
  | DC1srtdefs xs -> 
      let () = dec1_srtdef_list_tr xs in dec1_list_tr_aux1 ds res
  | DC1stacons (s1t, xs) -> 
      let s2t = srt1_tr s1t in
      let () = dec1_stacon_list_tr s2t xs in dec1_list_tr_aux1 ds res
  | DC1stacsts xs -> 
      let () = dec1_stacst_list_tr xs in dec1_list_tr_aux1 ds res
  | DC1stavars xs ->
      let xs = dec1_stavar_list_tr xs in
      let d2 = dec2_stavars d.dec1_loc xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1datsrts (xs: dec1_datsrt list) ->
      let () = dec1_datsrt_list_tr xs in dec1_list_tr_aux1 ds res
  | DC1sexpdefs (os1t, xs) ->
      let os2t = srt1_opt_tr os1t in
      let () = dec1_sexpdef_list_tr false os2t xs in
	dec1_list_tr_aux1 ds res
  | DC1typedefrecs (xs: dec1_sexpdef list) ->
      let () = dec1_sexpdef_list_tr true (Some srt2_type) xs in
	dec1_list_tr_aux1 ds res
  | DC1viewtypedefrecs (xs: dec1_sexpdef list) ->
      let () = dec1_sexpdef_list_tr true (Some srt2_viewtype) xs in
	dec1_list_tr_aux1 ds res
  | DC1sasps (xs: dec1_sasp list) ->
      let xs = dec1_sasp_list_tr xs in
      let d2 = dec2_sasps d.dec1_loc xs in
	dec1_list_tr_aux1 ds (d2 :: res)	
  | DC1extype (name, s1e_def) ->
      let s2e_def = sexp1_tr_dn_viewt0ype s1e_def in
      let d2 = dec2_extype d.dec1_loc name s2e_def in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1extval (name, d1e_def) ->
      let d2e_def = dexp1_tr d1e_def in
      let d2 = dec2_extval d.dec1_loc name d2e_def in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1dyncsts (dck, s1qss, xs) ->
      let () = SEnv2.SEXP2env.push () in
      let decarg = squas1_list_tr s1qss in
      let xs = dec1_dyncst_list_tr dck decarg xs in
      let () = SEnv2.SEXP2env.pop () in
      let d2 = dec2_dyncsts d.dec1_loc dck xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1data (dtk, starg, xs1, xs2) ->
      let s2tvs = List.map srt2_var_make starg in
      let s2cs = dec1_dat_list_tr dtk s2tvs xs1 xs2 in
      let d2 = dec2_data d.dec1_loc dtk s2cs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1modtypes (is_prop, xs) ->
      let () = dec1_modtype_list_tr is_prop xs in
	dec1_list_tr_aux1 ds res
  | DC1exns xs ->
      let xs = dec1_exn_list_tr xs in
      let d2 = dec2_exns d.dec1_loc xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1macdefs (is_abbrev, xs) ->
      let () = dec1_macdef_list_tr is_abbrev xs in
	dec1_list_tr_aux1 ds res
  | DC1overload (name, qid) ->
      let () = dec1_overload_tr_if d.dec1_loc name qid in
	dec1_list_tr_aux1 ds res
  | DC1funs (fk, starg, s1qss, xs) ->
      let s2tvs = List.map srt2_var_make starg in
      let () = SEnv2.SRT2env.push () in
      let () = SEnv2.srt2_env_add_var_list s2tvs in
      let () = SEnv2.SEXP2env.push () in
      let decarg = squas1_list_tr s1qss in 
      let istemp = match decarg with [] -> false | _ -> true in
      let xs = dec1_fun_list_tr fk s2tvs decarg xs in
      let () = SEnv2.SEXP2env.pop () in
      let () = SEnv2.SRT2env.pop () in
      let d2 = dec2_funs d.dec1_loc istemp fk xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1vals (vk, xs) ->
      let xs = dec1_val_list_tr false(*is_recursive*) xs in
      let d2 = dec2_vals d.dec1_loc vk xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1valpars xs ->
      let xs = dec1_val_list_tr false(*is_recursive*) xs in
      let d2 = dec2_valpars d.dec1_loc xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1valrecs xs ->
      let xs = dec1_val_list_tr true(*is_recursive*) xs in
      let d2 = dec2_valrecs d.dec1_loc xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1vars (is_stack, xs) ->
      let xs = dec1_var_list_tr xs in
      let d2 = dec2_vars d.dec1_loc is_stack xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1impls (decarg, xs) ->
      let xs = dec1_impl_list_tr decarg xs in
      let d2 = dec2_impls d.dec1_loc xs in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1local (head, body) ->
      let d2 = dec1_local_tr d.dec1_loc head body in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1staload (osid, filename, is_loaded, staload_res) ->
      let d2 = dec1_staload_tr
        d.dec1_loc osid filename is_loaded staload_res in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1dynload filename ->
      let d2 = dec2_dynload d.dec1_loc filename in
	dec1_list_tr_aux1 ds (d2 :: res)
  | DC1extern (position, code) ->
      let d2 = dec2_extern d.dec1_loc position code in
	dec1_list_tr_aux1 ds (d2 :: res)
end (* end of [dec1_list_tr_aux2] *)

and dec1_list_tr (ds: dec1 list): dec2 list = dec1_list_tr_aux1 ds []

(* ****** ****** *)

(* initialization *)

let initialize () = begin
  SDEnv2.initialize (); (* initializing static enviroment *)
  NS.initialize (); (* initializing namespace *)
end (* end of [initialize] *)

(* ****** ****** *)

(* end of [ats_trans2.ml] *)
