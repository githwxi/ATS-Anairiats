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
open Ats_stacst2
open Ats_misc

module P = Printf

module Cnt = Ats_counter
module Eff = Ats_effect
module Err = Ats_error
module Lab = Ats_label
module Loc = Ats_location
module PFc = Ats_printf_c
module SB = Ats_svar_bind
module SS = Ats_svar_stamp
module Sym = Ats_symbol
module Syn = Ats_syntax

(* ****** ****** *)

type lab = Lab.label
type loc = Loc.location
type stamp = Cnt.count

(* ****** ****** *)

(* a standard error reporting functions *)

let error (msg: string): 'a = Err.error ("ats_staexp2_util: " ^ msg)

(* ****** ****** *)

(* sort equality *)

let stb2_eq (st2b1: srt2_bas) (st2b2: srt2_bas): bool =
  match st2b1, st2b2 with
    | SRT2BASpre id1, SRT2BASpre id2 -> Syn.srt_id_eq id1 id2
    | SRT2BASdef ds1, SRT2BASdef ds2 ->
	Cnt.eq ds1.srt2_dat_stamp ds2.srt2_dat_stamp
    | _, _ -> false
(* end of [stb2_eq] *)

let stb2_leq (st2b1: srt2_bas) (st2b2: srt2_bas): bool =
  match st2b1, st2b2 with
    | SRT2BASpre id1, SRT2BASpre id2 -> Syn.srt_id_eq id1 id2
    | SRT2BASimp (id1, prf1, lin1), SRT2BASimp (id2, prf2, lin2) ->
	(prf1 <= prf2) && (lin1 <= lin2)
    | SRT2BASdef ds1, SRT2BASdef ds2 ->
	Cnt.eq ds1.srt2_dat_stamp ds2.srt2_dat_stamp
    | _, _ -> false
(* end of [stb2_leq] *)

(* ****** ****** *)

(*

let srt2_sel (s2t: srt2) (i: int): srt2 =
  let rec aux i s2ts = match s2ts with
    | s2t :: s2ts -> if i == 0 then s2t else aux (i-1) s2ts
    | [] -> error "srt2_sel: illegal index" in
    match s2t with
      | SRT2tup s2ts -> aux i s2ts
      | _ -> begin
	  P.eprintf "srt2_sel: not a tuple sort: %a\n" fprint_srt2 s2t;
	  Err.abort ();
	end

*)

(* ****** ****** *)

let srt2_solve (os2t1: srt2 option) (s2t2: srt2): unit =
  match os2t1 with
    | Some s2t1 -> begin match s2t1 with
	| SRT2ref r -> r := Some s2t2
	| _ -> begin
	    P.eprintf
	      "srt2_solve: not a sort reference: %a\n" fprint_srt2 s2t1;
	    Err.abort ();
	  end
      end
    | None -> error "srt2_solve: None"
(* end of [srt2_solve] *)

let rec srt2_link_rmv (s2t: srt2): srt2 = match s2t with
  | SRT2ref r -> begin match !r with
      | Some s2t ->
	  let s2t = srt2_link_rmv s2t in (r := Some s2t; s2t)
      | None -> s2t
    end
  | _ -> s2t
(* end of [srt2_link_rmv] *)

(* ****** ****** *)

let rec srt2_leq (s2t1: srt2) (s2t2: srt2): bool =
  let s2t1 = srt2_link_rmv s2t1
  and s2t2 = srt2_link_rmv s2t2 in match s2t1, s2t2 with
    | SRT2bas st2b1, SRT2bas st2b2 -> stb2_leq st2b1 st2b2
    | SRT2fun (s2ts1, s2t1), SRT2fun (s2ts2, s2t2) ->
	srt2_list_leq s2ts2 s2ts1 && srt2_leq s2t1 s2t2
    | SRT2tup s2ts1, SRT2tup s2ts2 -> srt2_list_leq s2ts1 s2ts2
    | SRT2ref r1, SRT2ref r2 -> r1 == r2
    | _, _ -> false
(* end of [srt2_leq] *)

and srt2_list_leq (s2ts1: srt2 list) (s2ts2: srt2 list): bool =
  match s2ts1, s2ts2 with
    | [], [] -> true
    | s2t1 :: s2ts1, s2t2 :: s2ts2 ->
	srt2_leq s2t1 s2t2 && srt2_list_leq s2ts1 s2ts2
    | _, _ -> false
(* end of [srt2_list_leq] *)

(* ****** ****** *)

let srt2_is_addr (s2t: srt2): bool = 
  match s2t with
    | SRT2bas st2b -> begin match st2b with
	| SRT2BASpre id -> Syn.srt_id_is_addr id | _ -> false
      end
    | _ -> false
(* end of [srt2_is_addr] *)

let srt2_is_bool (s2t: srt2): bool = 
  match s2t with
    | SRT2bas st2b -> begin match st2b with
	| SRT2BASpre id -> Syn.srt_id_is_bool id | _ -> false
      end
    | _ -> false
(* end of [srt2_is_bool] *)

let srt2_is_int (s2t: srt2): bool = 
  match s2t with
    | SRT2bas st2b -> begin match st2b with
	| SRT2BASpre id -> Syn.srt_id_is_int id | _ -> false
      end
    | _ -> false
(* end of [srt2_is_int] *)

let srt2_is_unit (s2t: srt2) =
  match s2t with SRT2tup [] -> true | _ -> false
(* end of [srt2_is_unit] *)

(* ****** ****** *)

let srt2_is_prop (s2t: srt2): bool = match s2t with
  | SRT2bas st2b -> begin match st2b with
      | SRT2BASimp (id, _, _) -> Syn.srt_id_is_prop id | _ -> false
    end
  | _ -> false
(* end of [srt2_is_prop] *)

let srt2_is_type (s2t: srt2): bool = match s2t with
  | SRT2bas st2b -> begin match st2b with
      | SRT2BASimp (id, _, _) -> Syn.srt_id_is_type id | _ -> false
    end
  | _ -> false
(* end of [srt2_is_type] *)

let srt2_is_t0ype (s2t: srt2): bool = match s2t with
  | SRT2bas st2b -> begin match st2b with
      | SRT2BASimp (id, _, _) -> Syn.srt_id_is_t0ype id | _ -> false
    end
  | _ -> false
(* end of [srt2_is_t0ype] *)

let srt2_is_view (s2t: srt2): bool = match s2t with
  | SRT2bas st2b -> begin match st2b with
      | SRT2BASimp (id, _, _) -> Syn.srt_id_is_view id | _ -> false
    end
  | _ -> false
(* end of [srt2_is_view] *)

let srt2_is_viewtype (s2t: srt2): bool = match s2t with
  | SRT2bas st2b -> begin match st2b with
      | SRT2BASimp (id, _, _) -> Syn.srt_id_is_viewtype id | _ -> false
    end
  | _ -> false
(* end of [srt2_is_viewtype] *)

let rec srt2_is_viewtype_fun (s2t: srt2) =
  match s2t with
    | SRT2fun (_, s2t) -> srt2_is_viewtype_fun s2t
    | _ -> srt2_is_viewtype s2t
(* end of [srt2_is_viewtype_fun] *)

let srt2_is_viewt0ype (s2t: srt2): bool = match s2t with
  | SRT2bas st2b -> begin match st2b with
      | SRT2BASimp (id, _, _) -> Syn.srt_id_is_viewt0ype id | _ -> false
    end
  | _ -> false
(* end of [srt2_is_viewt0ype] *)

(* ****** ****** *)

let srt2_is_types (s2t: srt2): bool = match s2t with
  | SRT2bas st2b -> begin match st2b with
      | SRT2BASimp (id, _, _) -> Syn.srt_id_is_types id | _ -> false
    end
  | _ -> false
(* end of [srt2_is_types] *)

(* ****** ****** *)

let srt2_is_linear (s2t: srt2): bool =
  match s2t with
    | SRT2bas st2b -> begin match st2b with
	| SRT2BASimp (id, _, lin) -> (lin > 0) | _ -> false
      end
    | _ -> false
(* end of [srt2_is_linear] *)

let srt2_is_proof (s2t: srt2): bool =
  match s2t with
    | SRT2bas st2b -> begin match st2b with
	| SRT2BASimp (id, prf, _) -> prf >= theProofLevel | _ -> false
      end
    | _ -> false
(* end of [srt2_is_proof] *)

let rec srt2_is_proof_fun (s2t: srt2): bool =
  match s2t with
    | SRT2fun (_, s2t) -> srt2_is_proof_fun s2t
    | _ -> srt2_is_proof s2t
(* end of [srt2_is_proof_fun] *)

let srt2_is_program (s2t: srt2): bool =
  match s2t with
    | SRT2bas st2b -> begin match st2b with
	| SRT2BASimp (id, prf, _) -> prf < theProofLevel | _ -> false
      end
    | _ -> false
(* end of [srt2_is_program] *)

let srt2_is_impredicative (s2t: srt2): bool =
  match s2t with
    | SRT2bas st2b -> begin
	match st2b with SRT2BASimp _ -> true | _ -> false
      end
    | _ -> false

let rec srt2_is_impredicative_fun (s2t: srt2): bool =
  match s2t with
    | SRT2fun (_, s2t) -> srt2_is_impredicative_fun s2t
    | _ -> srt2_is_impredicative s2t
(* end of [srt2_is_impredicative_fun] *)

let srt2_is_boxed (s2t: srt2): bool =
  match s2t with
    | SRT2bas st2b -> begin match st2b with
	| SRT2BASimp (id, prf, _) -> (prf = 0) | _ -> false
      end
    | _ -> false
(* end of [srt2_is_boxed] *)

let rec srt2_is_boxed_fun (s2t: srt2): bool =
  match s2t with
    | SRT2fun (_, s2t) -> srt2_is_boxed_fun s2t
    | _ -> srt2_is_boxed s2t
(* end of [srt2_is_boxed_fun] *)

(* ****** ****** *)

let srt2_fun_lin_prf
  (is_lin: bool) (is_prf: bool): srt2 = begin
  if is_prf then begin
    if is_lin then srt2_view else srt2_prop
  end else begin
    if is_lin then srt2_viewtype else srt2_type
  end
end (* end of [srt2_funclo] *)

(* ****** ****** *)

let sexp2_is_proof (s2e: sexp2): bool =
  srt2_is_proof (s2e.sexp2_sort)
let sexp2_is_proof_fun (s2e: sexp2): bool =
  srt2_is_proof_fun (s2e.sexp2_sort)
let sexp2_is_linear (s2e: sexp2): bool =
  srt2_is_linear (s2e.sexp2_sort)
let sexp2_is_nonlin (s2e: sexp2): bool =
  not (srt2_is_linear s2e.sexp2_sort)
let sexp2_is_impredicative (s2e: sexp2): bool =
  srt2_is_impredicative s2e.sexp2_sort

(* ****** ****** *)

(* datatype with one constructor *)
let scst2_is_singular (s2c: scst2): bool =
  match s2c.scst2_cons with Some [_] -> true | _ -> false

let scst2_is_list_like (s2c: scst2): bool =
  match s2c.scst2_islst with None -> false | Some _ -> true

(* ****** ****** *)

let scst2_select_with_argsorts
  (s2cs: scst2 list) (s2tss: (srt2 list) list): scst2 list =
  let rec aux s2t = function
    | s2ts :: s2tss -> begin match un_srt2_fun s2t with
	| Some (s2ts', s2t') ->
	    srt2_list_leq s2ts s2ts' && aux s2t' s2tss
	| None -> false
      end
    | [] -> true in
    List.filter (function s2c -> aux s2c.scst2_sort s2tss) s2cs
(* end of [ scst2_select_with_argsorts] *)

(* ****** ****** *)

let dcon2_make
  (loc: loc)
  (s2c: scst2)
  (name: Syn.did)
  (filename: Fil.filename)
  (vwtp: bool)
  (qua: (svar2 list * sexp2 list) list)
  (npf_s2es_arg: int_sexp2_list)
  (os2es_ind: (sexp2 list) option)
  : dcon2 =
  let fullname_id =
    let name_id =
      string_identifize (Syn.string_of_did name) in
      P.sprintf "%s__%s"
	(Fil.filename_fullname_id filename) name_id in
  let stamp = Cnt.dcon2_new_stamp () in
  let arity_full =
    let (npf, s2es) = npf_s2es_arg in List.length s2es in
  let arity_real =
    let rec aux1 i s2es = match s2es with
      | _ :: s2es1 -> if i > 0 then aux1 (i-1) s2es1 else s2es
      | [] -> [] in
    let rec aux2 i = function
      | s2e :: s2es ->
	  if srt2_is_proof (s2e.sexp2_sort) then aux2 i s2es
	  else aux2 (i+1) s2es
      | [] -> i in
    let (npf, s2es) = npf_s2es_arg in aux2 0 (aux1 npf s2es) in
  let s2e =
    let rec aux s2e = function
      | [] -> s2e
      | (s2vs, s2ps) :: qua -> sexp2_uni s2vs s2ps (aux s2e qua) in
    let s2e_res = match os2es_ind with
      | None -> sexp2_cst s2c
      | Some s2es -> sexp2_cstapp s2c s2es in
      aux (sexp2_fun_con npf_s2es_arg s2e_res) qua in {
      dcon2_loc= loc;
      dcon2_name= name;
      dcon2_filename= filename;
      dcon2_fullname_id= fullname_id;
      dcon2_scst= s2c;
      dcon2_vwtp= vwtp;
      dcon2_qua= qua;
      dcon2_arg= npf_s2es_arg;
      dcon2_arity_full= arity_full;
      dcon2_arity_real= arity_real;
      dcon2_ind= os2es_ind;
      dcon2_type= s2e;
      dcon2_tag= -1;
      dcon2_stamp= stamp;
    }
(* end of [dcon2_make] *)

let dcon2_is_exn (d2c: dcon2): bool =
  Exception_viewtype.eq_cst d2c.dcon2_scst

let dcon2_is_list_like (d2c: dcon2): bool =
  scst2_is_list_like (d2c.dcon2_scst)

let dcon2_is_nil_like (d2c: dcon2): bool =
  let s2c = d2c.dcon2_scst in
    match s2c.scst2_islst with
      | None -> false | Some (d2c_nil, _) -> dcon2_eq d2c d2c_nil

let dcon2_is_cons_like (d2c: dcon2): bool =
  match (d2c.dcon2_scst).scst2_islst with
    | None -> false | Some (_, d2c_cons) -> dcon2_eq d2c d2c_cons
(* end of [dcon2_is_cons] *)

let dcon2_is_singular (d2c: dcon2): bool =
  scst2_is_singular (d2c.dcon2_scst)

(* ****** ****** *)

let seff2_union (sf2e1: seff2) (sf2e2: seff2): seff2 =
  match sf2e1, sf2e2 with
    | SEFF2all, _ -> SEFF2all
    | _, SEFF2all -> SEFF2all
    | SEFF2nil, _ -> sf2e2
    | _, SEFF2nil -> sf2e1
    | SEFF2set (effs1, s2es1), SEFF2set (effs2, s2es2) ->
	SEFF2set (Eff.effset_union effs1 effs2, s2es1 @ s2es2)
(* end of [seff2_union] *)

let seff2_add_eff (sf2e: seff2) (eff: Eff.effect): seff2 =
  match sf2e with
    | SEFF2all -> SEFF2all
    | SEFF2nil ->
	let effs = Eff.effset_add Eff.effset_nil eff in SEFF2set (effs, [])
    | SEFF2set (effs, s2es) ->
	let effs = Eff.effset_add effs eff in SEFF2set (effs, s2es)
(* end of [seff2_add_eff] *)

(* ****** ****** *)

let sexp2_app (s2e_fun: sexp2) (s2es_arg: sexp2 list): sexp2 =
  let s2t_res = match un_srt2_fun s2e_fun.sexp2_sort with
    | Some (_, s2t) -> s2t
    | None -> error_of_deadcode "ats_staexp2_util: sexp2_app" in
    sexp2_app_with_sort s2t_res s2e_fun s2es_arg
(* end of [sexp2_app] *)

let sexp2_clo (knd: int) (s2e_fun: sexp2): sexp2 =
  let s2t_clo = match knd with
    | 0 -> if sexp2_is_linear s2e_fun then srt2_viewt0ype else srt2_t0ype
    | 1 -> srt2_viewtype
    | _ -> srt2_type in
    sexp2_clo_with_sort s2t_clo knd s2e_fun
(* end of [sexp2_clo] *)

let sexp2_funclo_with_sort (s2t_fun: srt2) (fc: Syn.funclo)
  (lin: int) (sf2e: seff2) (ns2es: int_sexp2_list) (s2e: sexp2): sexp2 =
  let s2e_fun = sexp2_fun_with_sort s2t_fun lin sf2e ns2es s2e in
    begin match fc with
      | Syn.FUNCLOclo knd -> sexp2_clo knd s2e_fun | Syn.FUNCLOfun -> s2e_fun
    end
(* end of [sexp2_funclo_with_sort] *)

let sexp2_top (s2e: sexp2): sexp2 =
  let s2t =
    let s2t = s2e.sexp2_sort in
      if srt2_is_proof s2t then srt2_prop else begin
	if srt2_is_boxed s2t then srt2_type else srt2_t0ype
      end in
    sexp2_top_with_sort s2t s2e
(* end of [sexp2_top] *)

let tyrec_is_singleton
  (npf: int) (ls2es: labsexp2 list): sexp2 option =
  let rec aux1 (i: int) (ls2es: labsexp2 list) =
    if i < npf then begin match ls2es with
      | ls2e :: ls2es -> aux1 (i+1) ls2es | [] -> None 
    end else begin
      aux2 None ls2es
    end
  and aux2 (os2e: sexp2 option) = function
    | (l, s2e) :: ls2es -> begin
	if sexp2_is_proof s2e then aux2 os2e ls2es
	else begin match os2e with
	  | None -> aux2 (Some s2e) ls2es
	  | Some _ -> None
	end
      end
    | [] -> os2e in
    aux1 0 ls2es
(* end of [tyrec_is_singleton] *)

let tytup_is_singleton
  (npf: int) (s2es: sexp2 list): sexp2 option =
  let rec aux1 (i: int) (s2es: sexp2 list) =
    if i < npf then begin match s2es with
      | s2e :: s2es -> aux1 (i+1) s2es | [] -> None
    end else begin
      aux2 None s2es
    end
  and aux2 (os2e: sexp2 option) (s2es: sexp2 list) =
    match s2es with
      | s2e :: s2es -> begin
	  if sexp2_is_proof s2e then aux2 os2e s2es
	  else begin match os2e with
	    | None -> aux2 (Some s2e) s2es
	    | Some _ -> None
	  end
	end
      | [] -> os2e in
    aux1 0 s2es
(* end of [tytup_is_singleton] *)

let srt2_tyrec (is_flat: bool) (is_lin: bool) (is_prf: bool): srt2 =
  if is_lin then begin
    if is_prf then srt2_view else
      (if is_flat then srt2_viewt0ype else srt2_viewtype)
  end else begin
    if is_prf then srt2_prop else
      (if is_flat then srt2_t0ype else srt2_type)
  end
(* end of [srt2_tyrec] *)

let srt2_singleton (is_lin: bool) (s2e: sexp2): srt2 = begin
  let s2t_s2e = s2e.sexp2_sort in
    if is_lin then begin
      if srt2_is_boxed s2t_s2e then srt2_viewtype else srt2_viewt0ype
    end else begin
      s2t_s2e (* [srt2_type] or [srt2_t0ype] *)
    end
end (* end of [srt2_singleton] *)

let sexp2_tyrec
  (k: tyrec_kind) (npf: int) (ls2es: labsexp2 list): sexp2 = begin
  let is_flat =
    match k with TYRECflt _ -> true | _ -> false in
  let (is_lin, is_prf) =
    let rec aux is_lin is_prf = function
      | (l, s2e) :: ls2es ->
	  let s2t = s2e.sexp2_sort in
	  let is_lin = is_lin || srt2_is_linear s2t in
	  let is_prf = is_prf && srt2_is_proof s2t in
	    aux is_lin is_prf ls2es
      | [] -> (is_lin, is_prf) in
      match ls2es with
	| _ :: _ -> aux false true ls2es | [] -> (false, false) in
  let s2t = srt2_tyrec is_flat is_lin is_prf in
  let s2t = 
    if is_flat then begin
      match tyrec_is_singleton npf ls2es with
	| Some s2e -> srt2_singleton is_lin s2e | None -> s2t
    end else begin
      s2t
    end in begin
      sexp2_tyrec_with_sort s2t k npf ls2es
    end
end (* end of [sexp2_tyrec] *)

let sexp2_union (s2i: sexp2) (ls2es: labsexp2 list): sexp2 =
  let is_lin =
    let rec aux is_lin = function
      | (l, s2e) :: ls2es ->
	  let s2t = s2e.sexp2_sort in
	    aux (is_lin || srt2_is_linear s2t) ls2es
      | [] -> is_lin in
      aux false ls2es in
  let s2t = if is_lin then srt2_viewt0ype else srt2_t0ype in
    sexp2_union_with_sort s2t s2i ls2es
(* end of [sexp2_union_with_sort] *)

(* ****** ****** *)

let sexp2_VarApp_app_with_sort
  (s2t: srt2) (s2e_fun: sexp2) (s2e_arg: sexp2): sexp2 =
  match s2e_fun.sexp2_node with
    | SE2Var s2V -> sexp2_VarApp_with_sort s2t s2V s2e_arg
    | _ -> sexp2_app_with_sort s2t s2e_fun [s2e_arg]
(* end of [sexp2_VarApp_app_with_sort] *)

(* ****** ****** *)

(* functions forming substitutions *)

type subst = (svar2 * sexp2) list

let sarg2_rbind  (* reverse bind: binding sarg2 to svar2  *)
  (name: Syn.sid) (os2t: srt2 option) (s2v: svar2): svar2 * svar2 =
  let s2v' = match os2t with
    | Some s2t -> begin
	if srt2_leq s2v.svar2_sort s2t then begin
          svar2_new_with_id name s2t
	end else let loc = Syn.loc_of_sid name in begin
	  P.eprintf "%a: sarg2_rbind: sort mismatch: %a <!= %a\n"
	    Loc.fprint loc fprint_srt2 s2t fprint_srt2 s2v.svar2_sort;
	  Err.abort ()
	end
      end
    | None -> svar2_new_with_id name s2v.svar2_sort in
    (s2v, s2v')
(* end of [sarg2_bind] *)

let sarg2_list_rbind loc0 (arg: sarg2 list) (s2vs: svar2 list)
  : (svar2 * svar2) list =
  let rec aux res arg s2vs = match arg, s2vs with
    | (name, os2t) :: arg, s2v :: s2vs ->
	aux (sarg2_rbind name os2t s2v :: res) arg s2vs
    | [], [] -> List.rev res
    | [], _ -> begin
	P.eprintf "%a: sarg2_list_rbind: too few arguments.\n" Loc.fprint loc0;
	Err.abort ();
      end
    | _, [] -> begin
	P.eprintf "%a: sarg2_list_rbind: too many arguments.\n" Loc.fprint loc0;
	Err.abort ();	  
      end in
    aux [] arg s2vs
(* end of [sarg2_list_rbind] *)

let svar2_bind loc0 (s2v: svar2) (s2v': svar2): svar2 * sexp2 =
  let s2t = s2v.svar2_sort and s2t' = s2v'.svar2_sort in
  if srt2_leq s2t' s2t then (s2v, sexp2_var s2v')
  else begin
    P.eprintf "%a: svar2_bind: sort mismatch: %a <!= %a\n"
      Loc.fprint loc0 fprint_srt2 s2t' fprint_srt2 s2t;
    Err.abort ();
  end
(* end of [svar2_bind] *)

let svar2_list_bind loc0 (s2vs: svar2 list) (s2vs': svar2 list): subst =
  let n = List.length s2vs and n' = List.length s2vs' in
    match compare n n' with
      | 0 -> List.map2 (svar2_bind loc0) s2vs s2vs'
      | i (* 1 or -1 *) -> begin
	  P.eprintf "%a: svar2_list_bind: unequal length.\n" Loc.fprint loc0;
	  Err.abort ();
	end
(* end of [svar2_list_bind] *)

let sexp2_bind loc0 (s2v: svar2) (s2e: sexp2): svar2 * sexp2 =
  let s2t1 = s2v.svar2_sort and s2t2 = s2e.sexp2_sort in
  if srt2_leq s2t2 s2t1 then (s2v, s2e) else begin
    P.eprintf "%a: sexp2_bind: sort mismatch: %a <!= %a\n"
      Loc.fprint loc0 fprint_srt2 s2t2 fprint_srt2 s2t1;
    Err.abort ();
  end
(* end of [sexp2_bind] *)

let sexp2_list_bind loc0 (s2vs: svar2 list) (s2es: sexp2 list): subst =
  let n1 = List.length s2vs and n2 = List.length s2es in
    match compare n1 n2 with
      | 0 -> List.map2 (sexp2_bind loc0) s2vs s2es
      | i -> begin
	  P.eprintf "%a: sexp2_list_bind: unequal length.\n" Loc.fprint loc0;
	  Err.abort ();
	end
(* end of [sexp2_list_bind] *)

(* labsexp2_list_bind: for modtype instantiation *)
let labsexp2_list_bind loc (ls2vs: labsvar2 list) (ls2es: labsexp2 list)
  : subst * svar2 list =
  let rec aux res1 res2 = function
    | (l, s2v) :: ls2vs, [] ->
	let s2v' = svar2_copy s2v in
	let s2e' = sexp2_var s2v' in
	  aux ((s2v, s2e') :: res1) (s2v' :: res2) (ls2vs, [])
    | (l, s2v) :: ls2vs, ((l', s2e) :: ls2es' as ls2es) ->
	if Lab.lt l l' then
	  let s2v' = svar2_copy s2v in
	  let s2e' = sexp2_var s2v' in
	    aux ((s2v, s2e') :: res1) (s2v' :: res2) (ls2vs, ls2es)
	else if Lab.eq l l' then
	  aux ((s2v, s2e) :: res1) res2 (ls2vs, ls2es')
	else begin
	  P.eprintf "%a: labsexp2_list_bind: unrecognized label <%a>\n"
	    Loc.fprint loc Lab.fprint l';
	  Err.abort ();
	end
    | [], [] -> (List.rev res1, List.rev res2)
    | [], (l', _) :: _ -> begin
	P.eprintf "%a: labsexp2_list_bind: unrecognized label <%a>\n"
	  Loc.fprint loc Lab.fprint l';
	Err.abort ();
      end in
    aux [] [] (ls2vs, ls2es)
(* end of [labsexp2_list_bind] *)

(* functions performing alpha and beta reductions *)

let subst_extend (sub: subst) (s2vs: svar2 list): subst * svar2 list =
  let rec aux sub s2vs' s2vs = match s2vs with
    | [] -> (sub, List.rev s2vs')
    | s2v :: s2vs ->
	let s2v' = svar2_copy s2v in
	  aux ((s2v, sexp2_var s2v') :: sub) (s2v' :: s2vs') s2vs in
    aux sub [] s2vs
(* end of [subst_extend] *)

let subst_extend_with_arg loc0 (sub: subst) (arg: sarg2 list) s2vs
  : subst * svar2 list =
  let rec aux sub s2vs' = function
    | ([], []) -> (sub, List.rev s2vs')
    | ((id, os2t) :: arg, s2v :: s2vs) ->
	let s2t = match os2t with
	  | None -> s2v.svar2_sort
	  | Some s2t ->
	      if srt2_leq s2v.svar2_sort s2t then s2t
	      else begin
		P.eprintf "%a: sort mistmatch: %a <!= %a\n"
		  Loc.fprint loc0 fprint_srt2 s2v.svar2_sort fprint_srt2 s2t;
		Err.abort ();
	      end in
	let s2v' = svar2_new_with_id id s2t in
	  aux ((s2v, sexp2_var s2v') :: sub) (s2v' :: s2vs') (arg, s2vs)
    | (_, _) -> begin
	P.eprintf "%a: subst_extend_with_arg: arity mistmatch\n"
	  Loc.fprint loc0;
	Err.abort ();
      end in
    aux sub [] (arg, s2vs)
(* end of [subst_extend_with_arg] *)

let rec sexp2_subst (sub: subst) (s2e0: sexp2): sexp2 =
  let s2t0 = s2e0.sexp2_sort in match s2e0.sexp2_node with
    | SE2app (s2e_fun, s2es_arg) -> 
	let s2e_fun = sexp2_subst sub s2e_fun in
	let s2es_arg =sexp2_list_subst sub s2es_arg in
	  sexp2_app_with_sort s2t0 s2e_fun s2es_arg
    | SE2char _ -> s2e0
    | SE2clo (knd, s2e_fun) ->
	let s2e_fun = sexp2_subst sub s2e_fun in
	  sexp2_clo knd s2e_fun
    | SE2cst s2c -> sexp2_cst (scst2_subst sub s2c)
    | SE2datcon (d2c, s2es_arg) ->
	let s2es_arg = sexp2_list_subst sub s2es_arg in
	  sexp2_datcon d2c s2es_arg
    | SE2datuni (d2c, s2es_arg) ->
	let s2es_arg = sexp2_list_subst sub s2es_arg in
	  sexp2_datuni d2c s2es_arg
    | SE2eff sf2e -> sexp2_eff (seff2_subst sub sf2e)
    | SE2eqeq (s2e1, s2e2) ->
	let s2e1 = sexp2_subst sub s2e1 in
	let s2e2 = sexp2_subst sub s2e2 in
	  sexp2_eqeq s2e1 s2e2
    | SE2exi (s2vs, s2es, s2e) ->
	let (sub, s2vs) = subst_extend sub s2vs in
	let s2es = sexp2_list_subst sub s2es in
	let s2e = sexp2_subst sub s2e in sexp2_exi s2vs s2es s2e
    | SE2extype _ -> s2e0
    | SE2fun (lin, sf2e, (npf, s2es), s2e) ->
	let sf2e = seff2_subst sub sf2e in
	let s2es = sexp2_list_subst sub s2es in
	let s2e = sexp2_subst sub s2e in
	  sexp2_fun_with_sort s2t0 lin sf2e (npf, s2es) s2e
    | SE2int _ -> s2e0
    | SE2lam (s2vs, s2e) ->
	let (sub, s2vs) = subst_extend sub s2vs in
	let s2e = sexp2_subst sub s2e in sexp2_lam_with_sort s2t0 s2vs s2e
    | SE2leq (s2e1, s2e2) ->
	let s2e1 = sexp2_subst sub s2e1 in
	let s2e2 = sexp2_subst sub s2e2 in
	  sexp2_leq s2e1 s2e2
    | SE2mfun (od2v, s2es, s2e) ->
	let s2es = sexp2_list_subst sub s2es in
	let s2e = sexp2_subst sub s2e in
	  sexp2_mfun od2v s2es s2e
    | SE2mlt (s2es1, s2es2) ->
	let s2es1 = sexp2_list_subst sub s2es1
	and s2es2 = sexp2_list_subst sub s2es2 in sexp2_mlt s2es1 s2es2
    | SE2out s2e -> let s2e = sexp2_subst sub s2e in sexp2_out s2e
    | SE2proj _ -> s2e0
    | SE2refarg (refval, s2e1, s2e2) -> begin
	let s2e1 = sexp2_subst sub s2e1 and s2e2 = sexp2_subst sub s2e2 in
	  sexp2_refarg refval s2e1 s2e2
      end (* end of [SE2refarg] *)
    | SE2sel (s2e, i) ->
	let s2e = sexp2_subst sub s2e in sexp2_sel_with_sort s2t0 s2e i
    | SE2top s2e ->
	let s2e = sexp2_subst sub s2e in sexp2_top_with_sort s2t0 s2e
    | SE2tup s2es ->
	let s2es = sexp2_list_subst sub s2es in sexp2_tup s2es
    | SE2tyarr (s2e_elt, s2ess_dim) ->
	let s2e_elt = sexp2_subst sub s2e_elt in
	let s2ess_dim = sexp2_list_list_subst sub s2ess_dim in
	  sexp2_tyarr s2e_elt s2ess_dim
    | SE2tylst s2es ->
	let s2es = sexp2_list_subst sub s2es in sexp2_tylst s2es
    | SE2tyrec (stamp, (npf, ls2es)) ->
	let ls2es = labsexp2_list_subst sub ls2es in
	  sexp2_tyrec_with_sort s2t0 stamp npf ls2es
    | SE2uni (s2vs, s2es, s2e) ->
	let (sub, s2vs) = subst_extend sub s2vs in
	let s2es = sexp2_list_subst sub s2es in
	let s2e = sexp2_subst sub s2e in sexp2_uni s2vs s2es s2e
    | SE2union (s2i, ls2es) ->
	let s2i = sexp2_subst sub s2i in
	let ls2es = labsexp2_list_subst sub ls2es in
	  sexp2_union_with_sort s2t0 s2i ls2es
    | SE2var s2v -> begin
	match svar2_subst sub s2v with None -> s2e0 | Some s2e -> s2e
      end
    | SE2Var s2V -> begin
        match sVar2_subst sub s2V with None -> s2e0 | Some s2e -> s2e
      end
    | SE2VarApp (s2V, s2e_arg) -> begin
        match sVar2_subst sub s2V with
	  | Some s2e ->
	      let s2e_arg = sexp2_subst sub s2e_arg in
		sexp2_VarApp_app_with_sort s2t0 s2e s2e_arg
	  | None ->
	      let s2e_arg = sexp2_subst sub s2e_arg in
		sexp2_VarApp_with_sort s2t0 s2V s2e_arg
      end
    | SE2vararg s2e ->
	let s2e = sexp2_subst sub s2e in sexp2_vararg s2e
(* end of [sexp2_subst] *)

and sexp2_list_subst
  (sub: subst) (s2es: sexp2 list): sexp2 list =
  List.map (sexp2_subst sub) s2es

and sexp2_list_list_subst
  (sub: subst) (s2ess: sexp2 list list): sexp2 list list =
  List.map (sexp2_list_subst sub) s2ess

and sexp2_opt_subst (sub: subst) (os2e: sexp2 option): sexp2 option =
  match os2e with None -> None | Some s2e -> Some (sexp2_subst sub s2e)
(* end of [sexp2_opt_subst] *)

and labsexp2_subst (sub: subst) ((l, s2e): labsexp2): labsexp2 =
  (l, sexp2_subst sub s2e)

and labsexp2_list_subst (sub: subst) (ls2es: labsexp2 list) : labsexp2 list =
  List.map (labsexp2_subst sub) ls2es

and seff2_subst (sub: subst) (sf2e: seff2): seff2 =
  match sf2e with
    | SEFF2all -> SEFF2all
    | SEFF2nil -> SEFF2nil
    | SEFF2set (effs, s2es) -> SEFF2set (effs, sexp2_list_subst sub s2es)
(* end of [seff2_subst] *)

and svar2_subst (sub: subst) (s2v: svar2): sexp2 option =
  let rec aux = function
    | [] -> None
    | (s2v', s2e) :: sub -> if s2v == s2v' then Some s2e else aux sub in
  aux sub
(* end of [svar2_subst] *)

and sVar2_subst (sub: subst) (s2V: sVar2): sexp2 option =
  match s2V.sVar2_link with
    | None -> begin
	let rec aux stamps = function
	  | [] -> stamps
	  | (s2v, s2e) :: sub ->
	      aux (Stamps.remove s2v.svar2_stamp stamps) sub in
	let stamps = aux (s2V.sVar2_svs) sub in
	let () = s2V.sVar2_svs <- stamps in
	  None
      end
    | Some s2e -> Some (sexp2_subst sub s2e)
(* end of [sVar2_subst] *)

and scst2_subst (sub: subst) (s2c: scst2): scst2 =
  let env = s2c.scst2_env in match env with
    | [] -> s2c (* abstract type is assumed to be closed *)
    | _ :: _ -> begin
	if scst2_is_recursive s2c then scst2_rec_subst sub s2c
	else begin match s2c.scst2_def with
	  | Some s2e -> begin
	      let env = sexp2_list_subst sub env in
	      let def = sexp2_subst sub s2e in {
		  scst2_name= s2c.scst2_name;
		  scst2_sort= s2c.scst2_sort;
		  scst2_isabs= None;
		  scst2_iscon= s2c.scst2_iscon;
		  scst2_isrec= false;
                  scst2_arity= s2c.scst2_arity;
		  scst2_arg= s2c.scst2_arg;
		  scst2_cons= s2c.scst2_cons;
		  scst2_islst= s2c.scst2_islst;
		  scst2_env= env;
		  scst2_def= Some def;
		  scst2_isasp= s2c.scst2_isasp;
		  scst2_stamp= s2c.scst2_stamp; (* The same stamp! *)
		  scst2_copy= None;
		}
	    end
	  | None -> begin
	      P.eprintf "ats_staexp2_util: scst2_subst: %a(%a)\n"
		fprint_scst2 s2c fprint_sexp2_list env;
	      Err.abort ();
	    end
	end
      end

and scst2_rec_subst (sub: subst) (s2c: scst2): scst2 =
  match s2c.scst2_copy with
    | Some s2c' -> s2c'
    | None -> begin
	let env = sexp2_list_subst sub (s2c.scst2_env) in
	let s2c' = {
	  scst2_name= s2c.scst2_name;
	  scst2_sort= s2c.scst2_sort;
	  scst2_isabs= None;
	  scst2_iscon= s2c.scst2_iscon;
	  scst2_isrec= true;
	  scst2_arity= s2c.scst2_arity;
	  scst2_arg= s2c.scst2_arg;
	  scst2_cons= s2c.scst2_cons;
	  scst2_islst= s2c.scst2_islst;
	  scst2_env= env;
	  scst2_def= None;
	  scst2_isasp= false;
	  scst2_stamp= s2c.scst2_stamp;
	  scst2_copy= None;
	} in
	let () = s2c.scst2_copy <- Some s2c' in
	  begin match s2c.scst2_def with
	    | Some s2e ->
		let s2e' = sexp2_subst sub s2e in
		let () = s2c'.scst2_def <- Some s2e' in
		let () = s2c.scst2_copy <- None in s2c'
	    | None -> begin
		P.eprintf "scst2_rec_subst: no definition: %a\n"
		  fprint_scst2 s2c;
		Err.abort ();
	      end
	  end
      end
(* end of [scst2_rec_subst] *)

(* ****** ****** *)

(* alpha conversion *)

let sexp2_alpha (s2v: svar2) (s2v': svar2) (s2e: sexp2): sexp2 =
  sexp2_subst [(s2v, sexp2_var s2v')] s2e

let sexp2_alpha_list
  (s2v: svar2) (s2v': svar2) (s2es: sexp2 list): sexp2 list =
  List.map (sexp2_alpha s2v s2v') s2es

(* ****** ****** *)

let rec sexp2_fvs (fvs: stamps) (bvs: stamps) (s2e0: sexp2): stamps =
  match s2e0.sexp2_node with
    | SE2app (s2e_fun, s2es_arg) -> begin
	let fvs = sexp2_fvs fvs bvs s2e_fun in sexp2_list_fvs fvs bvs s2es_arg
      end (* end of [SE2app] *)
    | SE2char _ -> fvs
    | SE2cst s2c -> scst2_fvs fvs bvs s2c
    | SE2clo (_(*knd*), s2e_fun) -> sexp2_fvs fvs bvs s2e_fun
    | SE2datcon (_(*d2c*), s2es_arg) -> sexp2_list_fvs fvs bvs s2es_arg
    | SE2datuni (_(*d2c*), s2es_arg) -> sexp2_list_fvs fvs bvs s2es_arg
    | SE2eff sf2e -> seff2_fvs fvs bvs sf2e
    | SE2eqeq (s2e1, s2e2) ->
	let fvs = sexp2_fvs fvs bvs s2e1 in sexp2_fvs fvs bvs s2e2
    | SE2exi (s2vs, s2es, s2e) -> begin
	let bvs = 
	  List.fold_left
	    (fun bvs s2v -> Stamps.add (s2v.svar2_stamp) bvs) bvs s2vs in
	let fvs = sexp2_list_fvs fvs bvs s2es in sexp2_fvs fvs bvs s2e
      end (* end of [S2Eexi] *)
    | SE2extype _ -> fvs
    | SE2fun (lin, sf2e, (npf, s2es), s2e) -> begin
	let fvs = seff2_fvs fvs bvs sf2e in
	let fvs = sexp2_list_fvs fvs bvs s2es in sexp2_fvs fvs bvs s2e
      end (* end of [SE2fun] *)
    | SE2int _ -> fvs
    | SE2lam (s2vs, s2e) -> begin
	let bvs = 
	  List.fold_left
	    (fun bvs s2v -> Stamps.add (s2v.svar2_stamp) bvs) bvs s2vs in
	  sexp2_fvs fvs bvs s2e
      end (* end of [SE2lam] *)
    | SE2leq (s2e1, s2e2) ->
	let fvs = sexp2_fvs fvs bvs s2e1 in sexp2_fvs fvs bvs s2e2
    | SE2mfun (od2v, s2es, s2e) ->
	let fvs = sexp2_list_fvs fvs bvs s2es in sexp2_fvs fvs bvs s2e
    | SE2mlt (s2es1, s2es2) -> begin
	let fvs = sexp2_list_fvs fvs bvs s2es1 in sexp2_list_fvs fvs bvs s2es2
      end (* end of [SE2mlt] *)
    | SE2out s2e -> sexp2_fvs fvs bvs s2e
    | SE2proj _ -> fvs
    | SE2refarg (_(*refval*), s2e1, s2e2) ->
	let fvs = sexp2_fvs fvs bvs s2e1 in sexp2_fvs fvs bvs s2e2
    | SE2sel (s2e, _) -> sexp2_fvs fvs bvs s2e
    | SE2top s2e -> sexp2_fvs fvs bvs s2e
    | SE2tup s2es -> sexp2_list_fvs fvs bvs s2es
    | SE2tyarr (s2e_elt, s2ess_dim) -> begin
	let fvs = sexp2_fvs fvs bvs s2e_elt in sexp2_list_list_fvs fvs bvs s2ess_dim
      end (* end of [SE2tyarr] *)
    | SE2tylst s2es -> sexp2_list_fvs fvs bvs s2es
    | SE2tyrec (stamp, (npf, ls2es)) -> labsexp2_list_fvs fvs bvs ls2es
    | SE2uni (s2vs, s2es, s2e) -> begin
	let bvs = 
	  List.fold_left
	    (fun bvs s2v -> Stamps.add (s2v.svar2_stamp) bvs) bvs s2vs in
	let fvs = sexp2_list_fvs fvs bvs s2es in sexp2_fvs fvs bvs s2e
      end (* end of [SE2uni] *)
    | SE2union (s2e, ls2es) ->
	let fvs = sexp2_fvs fvs bvs s2e in labsexp2_list_fvs fvs bvs ls2es
    | SE2var s2v -> svar2_fvs fvs bvs s2v
    | SE2Var s2V -> sVar2_fvs fvs bvs s2V
    | SE2VarApp (s2V, arg) ->
	let fvs = sVar2_fvs fvs bvs s2V in sexp2_fvs fvs bvs arg
    | SE2vararg s2e -> sexp2_fvs fvs bvs s2e
(* end of [sexp2_fvs] *)

and sexp2_list_fvs (fvs: stamps) (bvs: stamps) (s2es: sexp2 list): stamps =
  List.fold_left (fun fvs s2e -> sexp2_fvs fvs bvs s2e) fvs s2es

and sexp2_list_list_fvs
  (fvs: stamps) (bvs: stamps) (s2ess: sexp2 list list): stamps =
  List.fold_left (fun fvs s2es -> sexp2_list_fvs fvs bvs s2es) fvs s2ess
(* end of [sexp2_list_list_fvs] *)

and labsexp2_list_fvs (fvs: stamps) (bvs: stamps) (ls2es: labsexp2 list): stamps =
  let aux fvs (l, s2e) = sexp2_fvs fvs bvs s2e in
  List.fold_left aux fvs ls2es
(* end of [labsexp2_list_fvs] *)

and sexp2_opt_fvs
  (fvs: stamps) (bvs: stamps) (os2e: sexp2 option): stamps =
  match os2e with None -> fvs | Some s2e -> sexp2_fvs fvs bvs s2e
(* end of [sexp2_opt_fvs] *)

and scst2_fvs (fvs: stamps) (bvs: stamps) (s2c: scst2): stamps =
  if scst2_is_abstract s2c then fvs (* abstract type needs to be closed *)
  else if scst2_is_recursive s2c then sexp2_list_fvs fvs bvs (s2c.scst2_env)
  else begin match s2c.scst2_def with
    | Some s2e -> sexp2_fvs fvs bvs s2e | None -> fvs 
  end
(* end of [scst2_fvs] *)

(* ****** ****** *)

and seff2_fvs
  (fvs: stamps) (bvs: stamps) (sf2e: seff2): stamps =
  match sf2e with
    | SEFF2all -> fvs | SEFF2nil -> fvs
    | SEFF2set (effs, s2es) -> sexp2_list_fvs fvs bvs s2es
(* end of [seff2_fvs] *)

and svar2_fvs (fvs: stamps) (bvs: stamps) (s2v: svar2): stamps =
  let stamp = s2v.svar2_stamp in
    if Stamps.mem stamp bvs then fvs else Stamps.add stamp fvs
(* end of [svar2_fvs] *)

and sVar2_fvs (fvs: stamps) (bvs: stamps) (s2V: sVar2): stamps =
  match s2V.sVar2_link with
    | None -> Stamps.union fvs (s2V.sVar2_svs)
    | Some s2e -> sexp2_fvs fvs bvs s2e
(* end of [sVar2_fvs] *)

let dcon2_fvs (fvs: stamps) (d2c: dcon2): stamps =
  let (bvs, fvs) =
    let rec aux bvs fvs = function
      | [] -> (bvs, fvs)
      | (s2vs, s2es) :: qua ->
	  let bvs = 
	    List.fold_left
	      (fun bvs s2v -> Stamps.add (s2v.svar2_stamp) bvs)
	      bvs s2vs in
	  let fvs = sexp2_list_fvs fvs bvs s2es in
	    aux bvs fvs qua in
      aux Stamps.empty fvs d2c.dcon2_qua in
  let fvs =
    let (npf, s2es) = d2c.dcon2_arg in sexp2_list_fvs fvs bvs s2es in
    match d2c.dcon2_ind with
      | Some s2es -> sexp2_list_fvs fvs bvs s2es | None -> fvs
(* en dof [dcon2_fvs] *)

let dcon2_list_fvs (d2cs: dcon2 list): stamps =
  List.fold_left (fun fvs d2c -> dcon2_fvs fvs d2c) Stamps.empty d2cs

let sexp2_fvs_0 (s2e: sexp2): stamps =
  sexp2_fvs (Stamps.empty) (Stamps.empty) s2e

let sexp2_list_of_stamps (stamps: stamps): sexp2 list =
  let aux (i: stamp) (s2es: sexp2 list): sexp2 list =
    match svar2_stamp_find i with
      | None -> error "sexp2_list_of_stamps"
      | Some s2v -> (sexp2_var s2v) :: s2es in
    Stamps.fold aux stamps []
(* end of [sexp2_list_of_stamps] *)

(* ****** ****** *)

let rec sexp2_occurs (s2V: sVar2) (s2e: sexp2): bool =
  match s2e.sexp2_node with
    | SE2app (s2e_fun, s2es_arg) ->
	sexp2_occurs s2V s2e_fun || sexp2_list_occurs s2V s2es_arg
    | SE2char _ -> false
    | SE2clo (_(*knd*), s2e_fun) -> sexp2_occurs s2V s2e_fun
    | SE2cst _ -> false
    | SE2datcon (d2c, s2es_arg) -> sexp2_list_occurs s2V s2es_arg
    | SE2datuni (d2c, s2es_arg) -> sexp2_list_occurs s2V s2es_arg
    | SE2eff _ -> false
    | SE2eqeq (s2e1, s2e2) ->
	sexp2_occurs s2V s2e1 || sexp2_occurs s2V s2e2
    | SE2exi (s2vs, s2es, s2e) ->
	sexp2_occurs s2V s2e || sexp2_list_occurs s2V s2es
    | SE2extype _ -> false
    | SE2fun (_(*lin*), sf2e, (_(*npf*), s2es), s2e) ->
	seff2_occurs s2V sf2e || sexp2_list_occurs s2V s2es || sexp2_occurs s2V s2e
    | SE2int _ -> false
    | SE2lam (s2vs, s2e) -> sexp2_occurs s2V s2e
    | SE2leq (s2e1, s2e2) ->
	sexp2_occurs s2V s2e1 || sexp2_occurs s2V s2e2
    | SE2out s2e -> sexp2_occurs s2V s2e
    | SE2proj _ -> false
    | SE2mfun (od2v, s2es, s2e) ->
	sexp2_list_occurs s2V s2es || sexp2_occurs s2V s2e
    | SE2mlt (s2es1, s2es2) ->
	sexp2_list_occurs s2V s2es1 || sexp2_list_occurs s2V s2es2
    | SE2refarg (_(*refval*), s2e1, s2e2) ->
	sexp2_occurs s2V s2e1 || sexp2_occurs s2V s2e2
    | SE2sel (s2e, _) -> sexp2_occurs s2V s2e
    | SE2top s2e -> sexp2_occurs s2V s2e
    | SE2tup s2es -> sexp2_list_occurs s2V s2es
    | SE2tyarr (s2e_elt, s2ess_dim) ->
	sexp2_occurs s2V s2e_elt || sexp2_list_list_occurs s2V s2ess_dim
    | SE2tylst s2es -> sexp2_list_occurs s2V s2es
    | SE2tyrec (stamp, (npf, ls2es)) -> labsexp2_list_occurs s2V ls2es
    | SE2uni (s2vs, s2es, s2e) ->
	sexp2_occurs s2V s2e || sexp2_list_occurs s2V s2es
    | SE2union (s2e, ls2es) ->
	sexp2_occurs s2V s2e || labsexp2_list_occurs s2V ls2es
    | SE2var s2v -> false
    | SE2Var s2V' -> begin
	match s2V'.sVar2_link with
	  | None -> sVar2_eq s2V s2V'
	  | Some s2e -> sexp2_occurs s2V s2e
      end
    | SE2VarApp (s2V', arg) -> begin
	match s2V'.sVar2_link with
	  | None -> sVar2_eq s2V s2V' || sexp2_occurs s2V arg
	  | Some s2e -> sexp2_occurs s2V s2e || sexp2_occurs s2V arg
      end
    | SE2vararg s2e -> sexp2_occurs s2V s2e
(* end of [sexp2_occurs] *)

and sexp2_list_occurs (s2V: sVar2) (s2es: sexp2 list): bool =
  List.exists (sexp2_occurs s2V) s2es

and sexp2_list_list_occurs (s2V: sVar2) (s2ess: sexp2 list list): bool =
  List.exists (sexp2_list_occurs s2V) s2ess

and labsexp2_occurs (s2V: sVar2) (l, s2e): bool =
  sexp2_occurs s2V s2e

and labsexp2_list_occurs (s2V: sVar2) (ls2es: labsexp2 list): bool =
  List.exists (labsexp2_occurs s2V) ls2es

and seff2_occurs (s2V: sVar2) (sf2e: seff2): bool =
  match sf2e with
    | SEFF2all -> false
    | SEFF2nil -> false
    | SEFF2set (_, s2es) -> sexp2_list_occurs s2V s2es
(* end of [seff2_occurs] *)

(* ****** ****** *)

let rec sexp2_head (s2e: sexp2): sexp2 =
  match s2e.sexp2_node with
    | SE2app (s2e_fun, _) -> sexp2_head s2e_fun | _ -> s2e
(* end of [sexp2_head] *)

let sexp2_head_var (s2e: sexp2): svar2 option =
  let s2e_head = sexp2_head s2e in
    match s2e_head.sexp2_node with SE2var s2v -> Some s2v | _ -> None
(* end of [sexp2_head_var] *)

(* ****** ****** *)

(* computing head normal form *)

let rec sexp2_link_rmv s2e0: sexp2 = match s2e0.sexp2_node with
  | SE2cst s2c -> begin
      if scst2_is_recursive s2c then s2e0
      else begin match s2c.scst2_def with
	| Some s2e -> sexp2_link_rmv s2e | None -> s2e0
      end
    end
  | SE2var s2v -> begin match SB.svar_find s2v with
      | None -> s2e0
      | Some s2e -> sexp2_link_rmv s2e
    end
    (* s2V cannot be updated as reduction is conditional! *)
  | SE2Var s2V -> begin match s2V.sVar2_link with
      | Some s2e -> sexp2_link_rmv s2e
      | None -> s2e0
    end
  | SE2VarApp (s2V, arg) -> begin match s2V.sVar2_link with
      | Some s2e ->
	  let s2e = sexp2_link_rmv s2e in
	  let () = s2V.sVar2_link <- Some s2e in 
	    sexp2_VarApp_app_with_sort s2e0.sexp2_sort s2e arg
      | None -> s2e0
    end
  | _ -> s2e0
(* end of [sexp2_link_rmv] *)

let rec sexp2_whnf (s2e0: sexp2): sexp2 =
  let s2t0 = s2e0.sexp2_sort in
  let s2e0 = sexp2_link_rmv s2e0 in match s2e0.sexp2_node with
    | SE2app (s2e1, s2es2) -> begin
	let s2e1_new = sexp2_whnf s2e1 in match s2e1_new.sexp2_node with
	  | SE2lam (s2vs, body) -> begin
	      let sub = sexp2_list_bind Loc.nonloc s2vs s2es2 in
		sexp2_whnf (sexp2_subst sub body)
	    end
	  | _ -> begin
	      if s2e1 == s2e1_new then s2e0 else
		sexp2_app_with_sort s2t0 s2e1_new s2es2
	    end
      end
    | SE2sel (s2e, i) -> begin
	let s2e_new = sexp2_whnf s2e in match s2e_new.sexp2_node with
	  | SE2tup s2es -> List.nth s2es i
	  | _ -> begin
	      if s2e == s2e_new then s2e0 else sexp2_sel_with_sort s2t0 s2e_new i
	    end
      end
    | SE2top s2e -> sexp2_topize s2e
    | _ -> s2e0
(* end of [sexp2_whnf] *)

and sexp2_topize (s2e0: sexp2): sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
    | SE2exi (_, _, s2e) -> sexp2_topize s2e
    | SE2top s2e -> sexp2_topize s2e
    | SE2tyarr (s2e_elt, s2ess_dim) ->
        sexp2_tyarr (sexp2_top s2e_elt) s2ess_dim
    | SE2tyrec (k, (npf, ls2es)) -> begin match k with
	| TYRECbox -> sexp2_top s2e0
	| _ -> begin
	    let s2t0 =
	      if sexp2_is_proof s2e0 then srt2_prop else srt2_t0ype in
	      sexp2_tyrec_with_sort s2t0 k npf
		(List.map (function (l, s2e) -> (l, sexp2_top s2e)) ls2es)
	  end
      end
    | SE2uni (_, _, s2e) -> sexp2_topize s2e
    | SE2union (s2i, ls2es) ->
	let s2t0 =
	  if sexp2_is_proof s2e0 then srt2_prop else srt2_t0ype in
	  sexp2_union_with_sort s2t0 sexp2_intinf_zero ls2es
    | _ -> sexp2_top s2e0
(* end of [sexp2_topize] *)

(* ****** ****** *)

(* This is a heavily used function *)
let rec sexp2_nf (s2e0: sexp2): sexp2 =
(*
  let () =
    P.fprintf stdout "sexp2_nf: s2e0 = %a\n" fprint_sexp2 s2e0 in
*)
  let s2t0 = s2e0.sexp2_sort in
  let s2e0 = sexp2_link_rmv s2e0 in match s2e0.sexp2_node with
    | SE2app (s2e_fun, s2es_arg) -> begin
	let s2e_fun = sexp2_nf s2e_fun in
	let s2es_arg = sexp2_list_nf s2es_arg in
	  match s2e_fun.sexp2_node with
	    | SE2lam (s2vs_fun_arg, s2e_fun_body) ->
		let sub = sexp2_list_bind Loc.nonloc s2vs_fun_arg s2es_arg in
		  sexp2_nf (sexp2_subst sub s2e_fun_body)
	    | _ -> sexp2_app_with_sort s2t0 s2e_fun s2es_arg
      end
    | SE2clo (knd, s2e_fun) ->
	let s2e_fun = sexp2_nf s2e_fun in sexp2_clo knd s2e_fun
    | SE2eff sf2e -> let sf2e = seff2_nf sf2e in sexp2_eff sf2e
    | SE2eqeq (s2e1, s2e2) ->
	let s2e1 = sexp2_nf s2e1 and s2e2 = sexp2_nf s2e2 in
	  sexp2_eqeq s2e1 s2e2
    | SE2exi (s2vs, s2ps, s2e) ->
	let s2ps = sexp2_list_nf s2ps and s2e = sexp2_nf s2e in
	  sexp2_exi s2vs s2ps s2e
    | SE2fun (lin, sf2e, (npf, s2es_arg), s2e_res) ->
	let sf2e = seff2_nf sf2e in
	let s2es_arg  = sexp2_list_nf s2es_arg in
	let s2e_res = sexp2_nf s2e_res in
	  sexp2_fun_with_sort s2t0 lin sf2e (npf, s2es_arg) s2e_res
    | SE2lam (s2vs_arg, s2e_body) ->
	let s2e_body = sexp2_nf s2e_body in
	  sexp2_lam_with_sort s2t0 s2vs_arg s2e_body
    | SE2leq (s2e1, s2e2) ->
	let s2e1 = sexp2_nf s2e1 and s2e2 = sexp2_nf s2e2 in
	  sexp2_leq s2e1 s2e2
    | SE2mfun (od2v, s2es_met, s2e_fun) ->
	let s2es_met = sexp2_list_nf s2es_met in
	let s2e_fun = sexp2_nf s2e_fun in
	  sexp2_mfun od2v s2es_met s2e_fun
    | SE2mlt (s2es1, s2es2) ->
	let s2es1 = sexp2_list_nf s2es1 and s2es2 = sexp2_list_nf s2es2 in
	  sexp2_mlt s2es1 s2es2
    | SE2out s2e -> sexp2_out (sexp2_nf s2e)
    | SE2refarg (refval, s2e1, s2e2) ->
	let s2e1 = sexp2_nf s2e1 and s2e2 = sexp2_nf s2e2 in
	  sexp2_refarg refval s2e1 s2e2
    | SE2sel (s2e, i) -> begin
	let s2e_new = sexp2_nf s2e in match s2e_new.sexp2_node with
	  | SE2tup s2es -> List.nth s2es i
	  | _ -> sexp2_sel_with_sort s2t0 s2e_new i
      end
    | SE2top s2e -> sexp2_topize (sexp2_nf s2e)
    | SE2tup s2es -> sexp2_tup (sexp2_list_nf s2es)
    | SE2tyarr (s2e_elt, s2ess_dim) ->
	let s2e_elt = sexp2_nf s2e_elt in
	let s2ess_dim = List.map sexp2_list_nf s2ess_dim in
	  sexp2_tyarr s2e_elt s2ess_dim
    | SE2tylst s2es -> sexp2_tylst (sexp2_list_nf s2es)
    | SE2tyrec (stamp, (npf, ls2es)) ->
	sexp2_tyrec_with_sort s2t0 stamp npf (labsexp2_list_nf ls2es)
    | SE2uni (s2vs, s2ps, s2e) ->
	let s2ps = sexp2_list_nf s2ps and s2e = sexp2_nf s2e in
	  sexp2_uni s2vs s2ps s2e
    | SE2union (s2i, ls2es) ->
	sexp2_union_with_sort s2t0 (sexp2_nf s2i) (labsexp2_list_nf ls2es)
    | SE2vararg s2e_arg -> sexp2_vararg (sexp2_nf s2e_arg)
    | _ -> s2e0
(* end of [sexp2_nf] *)

and sexp2_list_nf (s2es: sexp2 list): sexp2 list =
  List.map sexp2_nf s2es

and labsexp2_list_nf (ls2es: labsexp2 list): labsexp2 list =
  List.map (function (l, s2e) -> (l, sexp2_nf s2e)) ls2es

and seff2_nf (sf2e: seff2): seff2 = match sf2e with
  | SEFF2all -> SEFF2all
  | SEFF2nil -> SEFF2nil
  | SEFF2set (effs, s2es) -> SEFF2set (effs, sexp2_list_nf s2es)
(* end of [seff2_nf] *)

(*

(* the following function is currently not in use *)
let rec sexp2_link_rmv_all s2e0: sexp2 =
  let s2t0 = s2e0.sexp2_sort in match s2e0.sexp2_node with
    | SE2app (s2e, s2es) ->
	let s2e = sexp2_link_rmv_all s2e in
	let s2es = sexp2_list_link_rmv_all s2es in
	  sexp2_app_with_sort s2t0 s2e s2es

    | SE2char _ -> s2e0

    | SE2cst s2c ->
	if scst2_is_recursive s2c then s2e0
	else begin match s2c.scst2_def with
	  | Some s2e ->
	      let s2e = sexp2_link_rmv_all s2e in
	      let () =
		if not (scst2_is_abstract s2c) then
		  s2e0.sexp2_node <- s2e.sexp2_node in s2e
	  | None -> s2e0
      end

    | SE2datcon (d2c, s2es_arg) ->
        let s2es_arg = sexp2_link_rmv_all s2es_arg in
          sexp2_datcon d2c s2es_arg

    | SE2datuni (d2c, s2es_arg) ->
        let s2es_arg = sexp2_link_rmv_all s2es_arg in
          sexp2_datuni d2c s2es_arg

    | SE2eff sf2e ->
	let sf2e = seff2_link_rmv_all sf2e in sexp2_eff sf2e

    | SE2eqeq (s2e1, s2e2) ->
	let s2e1 = sexp2_link_rmv_all s2e1 in
	let s2e2 = sexp2_link_rmv_all s2e2 in
	  sexp2_eqeq s2e1 s2e2

    | SE2exi (s2vs, s2es, s2e) ->
      let s2es = sexp2_list_link_rmv_all s2es in
      let s2e = sexp2_link_rmv_all s2e in
	sexp2_exi s2vs s2es s2e

    | SE2extype _ -> s2e0

    | SE2fun (fcr, lin, sf2e, (npf, s2es), s2e) ->
	let sf2e = seff2_link_rmv_all sf2e in
	let s2es = sexp2_list_link_rmv_all s2es in
	let s2e = sexp2_link_rmv_all s2e in
	  sexp2_fun_with_sort s2t0 fcr lin sf2e (npf, s2es) s2e

    | SE2int _ -> s2e0

    | SE2lam (s2vs, s2e) ->
	let s2e = sexp2_link_rmv_all s2e in
	  sexp2_lam_with_sort s2t0 s2vs s2e

    | SE2leq (s2e1, s2e2) ->
	let s2e1 = sexp2_link_rmv_all s2e1 in
	let s2e2 = sexp2_link_rmv_all s2e2 in
	  sexp2_leq s2e1 s2e2

    | SE2proj _ -> s2e0

    | SE2mfun (od2v, s2es_met, s2e_fun) ->
	let s2es_met = sexp2_list_link_rmv_all s2es_met in
	let s2e_fun = sexp2_link_rmv_all s2e_fun in
	  sexp2_mfun od2v s2es_met s2e_fun

    | SE2mlt (s2es1, s2es2) ->
	let s2es1 = sexp2_list_link_rmv_all s2es1 in
	let s2es2 = sexp2_list_link_rmv_all s2es2 in
	  sexp2_mlt s2es1 s2es2

    | SE2out s2e -> sexp2_out (sexp2_link_rmv_all s2e)

    | SE2refarg (refval, s2e1, s2e2) ->
	let s2e1 = sexp2_link_rmv_all s2e1 in
	let s2e2 = sexp2_link_rmv_all s2e2 in
	  sexp2_refarg refval s2e1 s2e2

    | SE2sel (s2e, i) ->
	sexp2_sel_with_sort s2t0 (sexp2_link_rmv_all s2e) i

    | SE2top s2e -> sexp2_top (sexp2_link_rmv_all s2e)

    | SE2tup s2es ->
	let s2es = sexp2_list_link_rmv_all s2es in sexp2_tup s2es

    | SE2tyarr (s2e_elt, s2ess_dim) ->
	let s2e_elt = sexp2_link_rmv_all s2e_elt in
	let s2ess_dim = List.map sexp2_list_link_rmv_all s2ess_dim in
	  sexp2_tyarr s2e_elt s2ess_dim

    | SE2tylst s2es ->
	let s2es = sexp2_list_link_rmv_all s2es in sexp2_tylst s2es

    | SE2tyrec (stamp, (npf, ls2es)) ->
	let ls2es = labsexp2_list_link_rmv_all ls2es in
	  sexp2_tyrec_with_sort s2t0 stamp npf ls2es

    | SE2uni (s2vs, s2es, s2e) ->
	let s2es = sexp2_list_link_rmv_all s2es in
	let s2e = sexp2_link_rmv_all s2e in
	  sexp2_uni s2vs s2es s2e

    | SE2union (s2e, ls2es) ->
	let s2e = sexp2_link_rmv_all s2e in
	let ls2es = labsexp2_list_link_rmv_all ls2es in
	  sexp2_union_with_sort s2t0 s2e ls2es

    | SE2var s2v -> begin
	match SB.svar_find s2v with
	  | None -> s2e0
	  | Some s2e -> sexp2_link_rmv_all s2e
      end

    | SE2Var s2V -> begin
	match s2V.sVar2_link with
	  | Some s2e -> sexp2_link_rmv_all s2e
	  | None ->
	      let () =
		s2V.sVar2_lbs <- sexp2_list_link_rmv_all s2V.sVar2_lbs in
	      let () =
		s2V.sVar2_ubs <- sexp2_list_link_rmv_all s2V.sVar2_ubs in
		s2e0
      end

    | SE2VarApp (s2V, arg) -> begin
	match s2V.sVar2_link with
	  | None -> sexp2_VarApp_with_sort s2t0 s2V (sexp2_link_rmv_all arg)
	  | Some s2e -> sexp2_VarApp_app_with_sort s2t0
	      (sexp2_link_rmv_all s2e) (sexp2_link_rmv_all arg)
      end

    | SE2vararg s2e ->
	let s2e = sexp2_link_rmv_all s2e in sexp2_vararg s2e

and sexp2_list_link_rmv_all s2es: sexp2 list =
  List.map sexp2_link_rmv_all s2es

and sexp2_opt_link_rmv_all os2e: sexp2 option =
  match os2e with
    | None -> None
    | Some s2e -> Some (sexp2_link_rmv_all s2e)

and labsexp2_link_rmv_all (l, s2e): labsexp2 =
  (l, sexp2_link_rmv_all s2e)

and labsexp2_list_link_rmv_all ls2es: labsexp2 list =
  List.map labsexp2_link_rmv_all ls2es

and seff2_link_rmv_all (sf2e: seff2): seff2 = match sf2e with
  | SEFF2all -> SEFF2all
  | SEFF2nil -> SEFF2nil
  | SEFF2set (effs, s2es) ->
      let s2es = sexp2_list_link_rmv_all s2es in SEFF2set (effs, s2es)

*)

(* ****** ****** *)

let rec sexp2_arity (s2e: sexp2): int list =
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2clo (_(*knd*), s2e) -> sexp2_arity s2e
    | SE2fun (_(*lin*), _(*sf2e*), (npf, s2es), s2e) ->
	let n = List.length s2es in n :: sexp2_arity s2e
    | SE2exi (_, _, s2e) -> sexp2_arity s2e
    | SE2uni (_, _, s2e) -> sexp2_arity s2e
    | SE2mfun (_, _, s2e) -> sexp2_arity s2e
    | _ -> []
(* end of [sexp2_arity] *)

(* ****** ****** *)

let rec sexp2_is_abscon (s2e: sexp2): bool =
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2cst s2c -> (scst2_is_abstract s2c || scst2_is_constructor s2c)
    | SE2app (s2e, _) -> sexp2_is_abscon s2e
    | _ -> false
(* end of [sexp2_is_abscon] *)

let sexp2_is_empty (s2e: sexp2): bool =
  match s2e.sexp2_node with
    | SE2extype name -> name = empty_type_name | _ -> false
(* end of [sexp2_is_empty] *)

let rec sexp2_is_metric (s2e: sexp2): bool =
  let s2e = sexp2_whnf s2e in
    begin match s2e.sexp2_node with
      | SE2clo (_, s2e) -> sexp2_is_metric s2e
      | SE2fun (_, _, _, s2e) -> sexp2_is_metric s2e
      | SE2mfun _ -> true
      | SE2uni (_, _, s2e) -> sexp2_is_metric s2e
      | _ -> false
    end
(* end of [sexp2_is_metric] *)

(* ****** ****** *)

let rec sexp2_proj_list (s2e: sexp2) (s2labs: slab2 list): sexp2 =
  match s2labs with
    | s2lab :: s2labs -> sexp2_proj_list (sexp2_proj s2e s2lab) s2labs
    | [] -> s2e
(* end of [sexp2_proj_list] *)

let sexp2_addr_norm (s2l0: sexp2): sexp2 * slab2 list =
  let rec aux s2labs s2l = match s2l.sexp2_node with
    | SE2proj (s2l, s2lab) -> aux (s2lab :: s2labs) s2l
    | _ -> (s2l, s2labs) in
    aux [] s2l0
(* end of [sexp2_addr_norm] *)

(* ****** ****** *)

let scst2_sizeof (s2c: scst2): szexp2 =
  if Void_t0ype.eq_cst s2c then szexp2_zero
  else if Byte_t0ype.eq_cst s2c then szexp2_byte 1
  else if (scst2_is_data s2c) then szexp2_word 1
  else SZE2cst (scst2_root s2c)

let rec sexp2_sizeof (s2e0: sexp2): szexp2 =
  let s2t0 = s2e0.sexp2_sort in
    if srt2_is_proof s2t0 then szexp2_zero
    else begin
      let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
	| SE2tyarr (s2e_elt, s2ess_ind) ->
	    SZE2tyarr (sexp2_sizeof s2e_elt, s2ess_ind)
	| SE2app (s2e1, s2es2) -> sexp2_sizeof s2e1
        | SE2clo (knd, _(*s2e_fun*)) ->
	    if knd = 0 then SZE2bot else szexp2_word 1
	| SE2cst s2c -> scst2_sizeof s2c
	| SE2datcon _ -> szexp2_word 1
	| SE2datuni _ -> szexp2_word 1
	| SE2exi (_, _, s2e) -> sexp2_sizeof s2e
	| SE2fun _ -> szexp2_word 1
	| SE2out s2e -> sexp2_sizeof s2e
	| SE2top s2e -> sexp2_sizeof s2e
	| SE2tyrec (k, (npf, ls2es)) -> begin match k with
	    | TYRECflt _ -> SZE2tyrec (k, labsexp2_list_sizeof ls2es)
	    | _ -> szexp2_word 1
	  end
	| SE2uni (_, _, s2e) -> sexp2_sizeof s2e
	| SE2union (s2i, ls2es) -> SZE2union (labsexp2_list_sizeof ls2es)
	| SE2var s2v -> SZE2var s2v
	| SE2Var s2V -> sVar2_sizeof s2V
	| _ -> begin
(*
	    let () = P.fprintf stdout "sexp2_sizeof: s2e0 = %a\n" fprint_sexp2 s2e0 in
*)
	      SZE2bot
	  end
    end
(* end of [sexp2_sizeof] *)

and labsexp2_list_sizeof (ls2es: labsexp2 list): labszexp2 list =
  List.map (function (l, s2e) -> (l, sexp2_sizeof s2e)) ls2es

and sVar2_sizeof (s2V: sVar2): szexp2 =
  match s2V.sVar2_lbs with
    | s2e :: _ -> sexp2_sizeof s2e
    | [] -> begin match s2V.sVar2_ubs with
	| s2e :: _ -> sexp2_sizeof s2e | [] -> SZE2bot
      end
(* end of [sVar2_sizeof] *)

(* ****** ****** *)

let rec szexp2_leq (sz2e1: szexp2) (sz2e2: szexp2): bool =
  match sz2e1, sz2e2 with
    | SZE2byte i1, SZE2byte i2 -> i1 <= i2
    | SZE2cst s2c1, SZE2cst s2c2 -> scst2_eq s2c1 s2c2
    | SZE2tyrec (k1, lsz2es1), SZE2tyrec (k2, lsz2es2) ->
	(tyrec_kind_eq k1 k2 && labszexp2_leq lsz2es1 lsz2es2)
    | SZE2union lsz2es1, SZE2union lsz2es2 -> labszexp2_leq lsz2es1 lsz2es2
    | SZE2var s2v1, SZE2var s2v2 -> svar2_eq s2v1 s2v2
    | SZE2word i1, SZE2word i2 -> i1 <= i2
    | _, _ -> false
(* end of [szexp2_leq] *)

and labszexp2_leq (lsz2es1: labszexp2 list) (lsz2es2: labszexp2 list): bool =
  match lsz2es1, lsz2es2 with
    | [], [] -> true
    | (l1, sz2e1) :: lsz2es1, (l2, sz2e2) :: lsz2es2 ->
	(Lab.eq l1 l2 && szexp2_leq sz2e1 sz2e2 && labszexp2_leq lsz2es1 lsz2es2)
    | _, _ -> false
(* end of [labszexp2_leq] *)

(* ****** ****** *)

let rec szexp2_syneq (sz2e1: szexp2) (sz2e2: szexp2): bool =
(*
  let () =
    P.fprintf stdout "szexp2_syneq: sz2e1 = %a\n" fprint_szexp2 sz2e1 in
  let () =
    P.fprintf stdout "szexp2_syneq: sz2e2 = %a\n" fprint_szexp2 sz2e2 in
*)
  match sz2e1, sz2e2 with
    | SZE2byte i1, SZE2byte i2 -> i1 = i2
    | SZE2cst s2c1, SZE2cst s2c2 -> scst2_eq s2c1 s2c2
    | SZE2out sz2e1, SZE2out sz2e2 -> szexp2_syneq sz2e1 sz2e2
    | SZE2tyarr (sz2e1_elt, s2ess1_dim), SZE2tyarr (sz2e2_elt, s2ess2_dim) ->
	szexp2_syneq sz2e1_elt sz2e2_elt && sexp2_list_list_syneq s2ess1_dim s2ess2_dim
    | SZE2tyrec (k1, lsz2es1), SZE2tyrec (k2, lsz2es2) ->
	(tyrec_kind_eq k1 k2 && labszexp2_syneq lsz2es1 lsz2es2)
    | SZE2union lsz2es1, SZE2union lsz2es2 -> labszexp2_syneq lsz2es1 lsz2es2
    | SZE2var s2v1, SZE2var s2v2 -> svar2_eq s2v1 s2v2
    | SZE2word i1, SZE2word i2 -> i1 = i2
    | _, _ -> false
(* end of [szexp2_syneq] *)

and labszexp2_syneq (lsz2es1: labszexp2 list) (lsz2es2: labszexp2 list): bool =
  match lsz2es1, lsz2es2 with
    | [], [] -> true
    | (l1, sz2e1) :: lsz2es1, (l2, sz2e2) :: lsz2es2 ->
	(Lab.eq l1 l2 && szexp2_syneq sz2e1 sz2e2 && labszexp2_syneq lsz2es1 lsz2es2)
    | _, _ -> false
(* end of [labszexp2_syneq] *)

(* ****** ****** *)

and szexp2_syneq_lab (sz2e1: szexp2) (sz2e2: szexp2): bool =
(*
  let () =
    P.fprintf stdout "szexp2_syneq_lab: sz2e1 = %a\n" fprint_szexp2 sz2e1 in
  let () =
    P.fprintf stdout "szexp2_syneq_lab: sz2e2 = %a\n" fprint_szexp2 sz2e2 in
*)
  match sz2e1, sz2e2 with
    | SZE2out sz2e1, _ -> szexp2_syneq_lab sz2e1 sz2e2
    | _, SZE2out sz2e2 -> szexp2_syneq_lab sz2e1 sz2e2
    | SZE2byte i1, SZE2byte i2 -> i1 = i2
    | SZE2cst s2c1, SZE2cst s2c2 -> scst2_eq s2c1 s2c2
    | SZE2tyarr (sz2e1_elt, s2ess1_dim), SZE2tyarr (sz2e2_elt, s2ess2_dim) ->
	if szexp2_syneq sz2e1_elt sz2e2_elt then
	  sexp2_list_list_syneq s2ess1_dim s2ess2_dim
	else false
    | SZE2tyrec (k1, lsz2es1), SZE2tyrec (k2, lsz2es2) ->
	(tyrec_kind_eq k1 k2 && labszexp2_syneq_lab lsz2es1 lsz2es2)
    | SZE2union lsz2es1, SZE2union lsz2es2 -> labszexp2_syneq_lab lsz2es1 lsz2es2
    | SZE2var s2v1, SZE2var s2v2 -> svar2_eq s2v1 s2v2
    | SZE2word i1, SZE2word i2 -> i1 = i2
    | _, _ -> false
(* end of [szexp2_syneq_lab] *)

and labszexp2_syneq_lab (lsz2es1: labszexp2 list) (lsz2es2: labszexp2 list): bool =
  match lsz2es1, lsz2es2 with
    | [], [] -> true
    | (l1, sz2e1) :: lsz2es1, (l2, sz2e2) :: lsz2es2 ->
	if Lab.eq l1 l2 then
	  szexp2_syneq_lab sz2e1 sz2e2 && labszexp2_syneq_lab lsz2es1 lsz2es2
	else false
    | _, _ -> false
(* end of [labszexp2_syneq_lab] *)

(* ****** ****** *)

and sexp2_syneq (s2e10: sexp2) (s2e20: sexp2): bool =
  let s2e10 = sexp2_whnf s2e10 and s2e20 = sexp2_whnf s2e20 in
(*
  let () =
    P.fprintf stdout "sexp2_syneq: s2e10 = %a\n" fprint_sexp2 s2e10 in
  let () =
    P.fprintf stdout "sexp2_syneq: s2e20 = %a\n" fprint_sexp2 s2e20 in
*)
    match s2e10.sexp2_node, s2e20.sexp2_node with
      | SE2app (s2e11, s2es12), SE2app (s2e21, s2es22) ->
	  sexp2_syneq s2e11 s2e21 && sexp2_list_syneq s2es12 s2es22
      | SE2char c1, SE2char c2 -> c1 == c2
      | SE2cst s2c1, SE2cst s2c2 -> scst2_eq s2c1 s2c2
      | SE2datcon (d2c1, s2es1_arg), SE2datcon (d2c2, s2es2_arg) ->
	  dcon2_eq d2c1 d2c2 && sexp2_list_syneq s2es1_arg s2es2_arg
      | SE2datuni (d2c1, s2es1_arg), SE2datuni (d2c2, s2es2_arg) ->
	  dcon2_eq d2c1 d2c2 && sexp2_list_syneq s2es1_arg s2es2_arg
      | SE2eqeq (s2e11, s2e12), SE2eqeq (s2e21, s2e22) ->
	  sexp2_syneq s2e11 s2e21 && sexp2_syneq s2e12 s2e22
      | SE2extype name1, SE2extype name2 -> name1 = name2
      | SE2leq (s2e11, s2e12), SE2leq (s2e21, s2e22) ->
	  sexp2_syneq s2e11 s2e21 && sexp2_syneq s2e12 s2e22
      | SE2int i1, SE2int i2 -> i1 == i2
      | SE2out s2e1, SE2out s2e2 -> sexp2_syneq s2e1 s2e2
      | SE2proj (s2l1, s2lab1), SE2proj (s2l2, s2lab2) ->
	  sexp2_syneq s2l1 s2l2 && slab2_syneq s2lab1 s2lab2
      | SE2refarg (refval1, s2e11, s2e12), SE2refarg (refval2, s2e21, s2e22) ->
	  refval1 = refval2 && sexp2_syneq s2e11 s2e21 && sexp2_syneq s2e12 s2e22
      | SE2sel (s2e1, i1), SE2sel (s2e2, i2) ->
	  i1 == i2 && sexp2_syneq s2e1 s2e2
      | SE2top s2e1, SE2top s2e2 ->
	  szexp2_syneq (sexp2_sizeof s2e1) (sexp2_sizeof s2e2)
      | SE2tup s2es1, SE2tup s2es2 -> sexp2_list_syneq s2es1 s2es2
      | SE2tyarr (s2e1_elt, s2ess1_ind), SE2tyarr (s2e2_elt, s2ess2_ind) ->
	  sexp2_syneq s2e1_elt s2e2_elt &&
	  sexp2_list_list_syneq s2ess1_ind s2ess2_ind
      | SE2tylst s2es1, SE2tylst s2es2 -> sexp2_list_syneq s2es1 s2es2
      | SE2tyrec (k1, (npf1, ls2es1)), SE2tyrec (k2, (npf2, ls2es2)) ->
	  tyrec_kind_eq k1 k2 && npf1 == npf2 && labsexp2_list_syneq ls2es1 ls2es2
      | SE2var s2v1, SE2var s2v2 -> svar2_eq s2v1 s2v2
      | SE2Var s2V1, SE2Var s2V2 -> sVar2_eq s2V1 s2V2
      | _, _ -> false
(* end of [sexp2_syneq] *)

and sexp2_list_syneq (s2es10: sexp2 list) (s2es20: sexp2 list): bool =
  match s2es10, s2es20 with
    | [], [] -> true
    | s2e1 :: s2es1, s2e2 :: s2es2 ->
	sexp2_syneq s2e1 s2e2 && sexp2_list_syneq s2es1 s2es2
    | _, _ -> false
(* end of [sexp2_list_syneq] *)

and sexp2_list_list_syneq
  (s2ess10: sexp2 list list) (s2ess20: sexp2 list list): bool =
  match s2ess10, s2ess20 with
    | [], [] -> true
    | s2es1 :: s2ess1, s2es2 :: s2ess2 ->
	sexp2_list_syneq s2es1 s2es2 && sexp2_list_list_syneq s2ess1 s2ess2
    | _, _ -> false
(* end of [sexp2_list_list_syneq] *)

and labsexp2_list_syneq (ls2es10: labsexp2 list) (ls2es20: labsexp2 list)
  : bool = match ls2es10, ls2es20 with
    | [], [] -> true
    | (l1, s2e1) :: ls2es1, (l2, s2e2) :: ls2es2 ->
	Lab.eq l1 l2 &&	sexp2_syneq s2e1 s2e2 && labsexp2_list_syneq ls2es1 ls2es2
    | _, _ -> false
(* end of [labsexp2_list_syneq] *)

and sexp2_opt_syneq (os2e1: sexp2 option ) (os2e2: sexp2 option): bool =
  match os2e1, os2e2 with
    | None, None -> true
    | Some s2e1, Some s2e2 -> sexp2_syneq s2e1 s2e2
    | _, _ -> false
(* end of [slab2_opt_syneq] *)

and slab2_syneq (s2lab1: slab2) (s2lab2: slab2): bool =
(*
  let () = begin
    P.fprintf stdout "slab2_syneq: \n";
    P.fprintf stdout "  s2lab1 = %a\n" fprint_slab2 s2lab1;
    P.fprintf stdout "  s2lab2 = %a\n" fprint_slab2 s2lab2;
  end in
*)
  match s2lab1, s2lab2 with
    | SL2lab1 (l1, s2e1), SL2lab1 (l2, s2e2) ->
	if Lab.eq l1 l2 then
	  szexp2_syneq_lab (sexp2_sizeof s2e1) (sexp2_sizeof s2e2)
	else false
    | SL2ind1 (ind1, s2e1), SL2ind1 (ind2, s2e2) ->
	sexp2_list_list_syneq ind1 ind2 && sexp2_syneq s2e1 s2e2
    | _, _ -> false
(* end of [slab2_syneq] *)

(* ****** ****** *)

let slab2_synleq (s2lab1: slab2) (s2lab2: slab2): bool =
  match s2lab1, s2lab2 with
    | SL2lab1 (l1, _), SL2lab0 l2 -> Lab.eq l1 l2
    | SL2lab1 (l1, _), SL2lab1 (l2, _) -> Lab.eq l1 l2
    | _, _ -> false
(* end of [slab2_synleq] *)

let slab2_list_synleq 
  (s2labs1: slab2 list) (s2labs2: slab2 list): bool =
  let rec aux s2labs1 s2labs2 = match s2labs1, s2labs2 with
    | [], [] -> true
    | s2lab1 :: s2labs1, s2lab2 :: s2labs2 ->
	slab2_synleq s2lab1 s2lab2 && aux s2labs1 s2labs2
    | _, _ -> false in
    aux s2labs1 s2labs2
(* end of [slab2_list_synleq] *)

let slab2_list_is_prefix
  (s2labs1: slab2 list) (s2labs2: slab2 list): slab2 list option =
  let rec aux s2labs1 s2labs2 = match s2labs1, s2labs2 with
    | [], _ -> Some s2labs2
    | _, [] -> None
    | s2lab1 :: s2labs1, s2lab2 :: s2labs2 ->
	if slab2_synleq s2lab1 s2lab2 then aux s2labs1 s2labs2 else None in
    aux s2labs1 s2labs2
(* end of [slab2_list_is_prefix] *)

(* ****** ****** *)

let slab2_list_trim (s2labs0_ft: slab2 list)
  (s2labs1_ft: slab2 list) (s2labs1_bk: slab2 list): slab2 list =
  let rec aux1 xs_pre xs_bk = match xs_pre, xs_bk with
    | _ :: xs_pre, _ :: xs_bk -> aux1 xs_pre xs_bk
    | [], _ -> xs_bk
    | _, _ -> error_of_deadcode "addr_assign_sel: aux1" in
  let rec aux2 xs_pre xs_ft xs_bk =
    match xs_pre, xs_ft with
      | _ :: xs_pre, _ :: xs_ft -> aux2 xs_pre xs_ft xs_bk
      | [], _ -> xs_ft @ xs_bk
      | _, [] -> aux1 xs_pre xs_bk in
    aux2 s2labs0_ft s2labs1_ft s2labs1_bk
(* end of [slab2_list_trim] *)

(* ****** ****** *)

let rec sexp2_synlt (s2e1: sexp2) (s2e2: sexp2): bool =
  let s2e2 = sexp2_whnf s2e2 in match s2e2.sexp2_node with
    | SE2app (_, s2es2) -> sexp2_list_synlte s2e1 s2es2
    | _ -> false
(* end of [sexp2_synlt] *)

and sexp2_synlte (s2e1: sexp2) (s2e2: sexp2): bool =
  sexp2_syneq s2e1 s2e2 || sexp2_synlt s2e1 s2e2

and sexp2_list_synlte (s2e1: sexp2) (s2es2: sexp2 list): bool =
  let rec aux s2es2 = match s2es2 with
    | [] -> false
    | s2e2 :: s2es2 ->
	sexp2_synlte s2e1 s2e2 || sexp2_list_synlte s2e1 s2es2 in
    aux s2es2
(* end of [sexp2_list_synlte] *)

(* ****** ****** *)

let sexp2_mlt_reduce
  (metric: sexp2 list) (metric_bound: sexp2 list): sexp2 =
  let aux_lt s2e1 s2e2: sexp2 =
    if srt2_is_int (s2e1.sexp2_sort) then
      let s2p = Ilt.make_exp (Some [s2e1; s2e2]) in s2p
    else sexp2_bool (sexp2_synlt s2e1 s2e2) in

  let aux_lte s2e1 s2e2: sexp2 =
    if srt2_is_int (s2e1.sexp2_sort) then
      let s2p = Ilte.make_exp (Some [s2e1; s2e2]) in s2p
    else sexp2_bool (sexp2_synlte s2e1 s2e2) in

  let rec aux_list s2es1 s2es2 = match s2es1, s2es2 with
    | [], [] -> sexp2_bool false
    | [s2e1], [s2e2] -> aux_lt s2e1 s2e2
    | s2e1 :: s2es1, s2e2 :: s2es2 ->
	let s2p_lt = aux_lt s2e1 s2e2 in
	let s2p_lte = aux_lte s2e1 s2e2 in 
	let s2p_rest = aux_list s2es1 s2es2 in
	  Badd.make_exp
	    (Some [s2p_lt; Bmul.make_exp (Some [s2p_lte; s2p_rest])])
    | _, _ -> error_of_deadcode "ats_staenv3: cstr3_metric" in
    aux_list metric metric_bound
(* end of [sexp2_mlt_reduce] *)

(* ****** ****** *)

let rec sexp2_unfold_opt (s2e0: sexp2): sexp2 option =
  match s2e0.sexp2_node with
    | SE2cst s2c ->
	if scst2_is_recursive s2c then s2c.scst2_def else None
    | SE2app (s2e, s2es) -> begin
	let s2t0 = s2e0.sexp2_sort in
	  match sexp2_unfold_opt s2e with
	    | Some s2e -> Some (sexp2_app_with_sort s2t0 s2e s2es)
	    | None -> None
      end
    | _ -> None
(* end of [sexp2_unfold_opt] *)

let rec sexp2_unfold loc (s2e: sexp2): sexp2 =
  match sexp2_unfold_opt s2e with
    | Some s2e -> s2e
    | None -> begin
	P.eprintf "%a: the static expression cannot be unfolded.\n"
	  Loc.fprint loc;
	Err.abort ();
      end
(* end of [sexp2_unfold] *)

let sexp2_cst_type loc stamps (s2c: scst2): sexp2 =
  let rec aux s2e = match s2e.sexp2_sort with
    | SRT2fun (s2ts, s2t) ->
	let s2es =
	  List.map
	    (function s2t -> sexp2_Var (sVar2_new loc stamps s2t))
	    s2ts in
	  aux (sexp2_app_with_sort s2t s2e s2es)
    | _ -> s2e in
    aux (sexp2_cst s2c)
(* end of [sexp2_cst_type] *)

(* ****** ****** *)

let labsexp2_list_select_get (ls2es: labsexp2 list) (l0: lab)
  : (int * sexp2) option =
  let rec aux i ls2es = match ls2es with
    | [] -> None
    | (l, s2e) :: ls2es ->
	if Lab.eq l0 l then Some (i, s2e) else aux (i+1) ls2es in
    aux 0 ls2es
(* end of [labsexp2_list_select_get] *)

let labsexp2_list_select_set (ls2es: labsexp2 list) (l0: lab) (s2e_new: sexp2)
  : (int * labsexp2 list) option =
  let rec aux ls2es = match ls2es with
    | [] -> None
    | (l, s2e) :: ls2es ->
	if Lab.eq l0 l then Some (0, (l, s2e_new) :: ls2es)
	else begin match aux ls2es with
	  | None -> None
	  | Some (i, ls2es) -> Some (i+1, (l, s2e) :: ls2es)
	end in
    aux ls2es
(* end of [labsexp2_list_select_set] *)

(* ****** ****** *)

let rec sexp2_select_lab loc0
  (s2e0: sexp2) (l0: lab): sexp2 (* type *) * bool (* linear residue *) =
  let rec aux_is_linear i ls2es = match ls2es with
    | [] -> false
    | (l, s2e) :: ls2es ->
	if i = 0 then 
	  List.exists (function (l, s2e) -> sexp2_is_linear s2e) ls2es
	else if sexp2_is_linear s2e then true
	else aux_is_linear (i - 1) ls2es in
  let aux s2e = match s2e.sexp2_node with
    | SE2tyrec (stamp, (npf, ls2es)) -> begin
	match labsexp2_list_select_get ls2es l0 with
	  | Some (i, s2e) ->
	      let is_lin = aux_is_linear i ls2es in (s2e, is_lin)
	  | None -> begin
	      P.eprintf
		"%a: sexp2_select_lab: the label <%a> is not found.\n"
		Loc.fprint loc0 Lab.fprint l0;
	      Err.abort ();
	    end
      end
    | _ -> begin
	P.eprintf "%a: sexp2_select: not a record type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e0;
	Err.abort ();
      end in
  let s2e0 = sexp2_whnf s2e0 in aux s2e0
(* end of [sexp2_select_lab] *)

let sexp2_select_list loc0 (s2e0: sexp2) (s2labs_nt: slab2 list)
  : sexp2 * bool (* linear residue *) * slab2 list (* typed labels *) =
  let rec aux (s2e0: sexp2) (is_lin0: bool) (s2labs: slab2 list) = function
    | s2lab_nt :: s2labs_nt ->
	let l = match s2lab_nt with
	  | SL2lab0 l -> l
	  | SL2lab1 (l, _) -> l (* deadcode *)
	  | _ -> begin
	      P.eprintf "%a: sexp2_select_list: illegal array subscription.\n"
		Loc.fprint loc0;
	      Err.abort ();
	    end in
	let (s2e, is_lin) = sexp2_select_lab loc0 s2e0 l in
	let is_lin0 = is_lin0 || is_lin in
	let s2labs = slab2_lab1 l s2e0 :: s2labs in
	  aux s2e is_lin0 s2labs s2labs_nt
    | [] -> (s2e0, is_lin0, List.rev s2labs) in
    aux s2e0 false [] s2labs_nt
(* end of [sexp2_select_list] *)

(* ****** ****** *)

let svar2_is_unisorted (s2v: svar2): bool =
  let s2t = s2v.svar2_sort in begin
    match srt2_link_rmv s2t with SRT2tup [] -> true | _ -> false
  end
(* end of [svar2_is_unisorted] *)

let svar2_is_unsorted (s2v: svar2): bool =
  match srt2_link_rmv (s2v.svar2_sort) with
    | SRT2ref r -> begin
	match !r with None -> true | Some _ -> false
      end
    | _ -> false
(* end of [svar2_is_unsorted] *)

let svar2_is_boxed (s2v: svar2): bool = begin
  let s2t = srt2_link_rmv (s2v.svar2_sort) in srt2_is_boxed s2t
end (* end of [svar2_is_boxed] *)

(* ****** ****** *)

let rec sexp2_is_var_res (s2e: sexp2): bool =
  let s2e = sexp2_whnf s2e in
    begin match s2e.sexp2_node with
      | SE2exi (_, _, s2e) -> sexp2_is_var_res s2e
      | SE2uni (_, _, s2e) -> sexp2_is_var_res s2e
      | SE2var s2v -> if svar2_is_boxed s2v then false else true
      | _ -> false
    end
(* end of [sexp2_is_var_res] *)

let rec sexp2_is_var_fun (s2e: sexp2): bool =
  let s2e = sexp2_whnf s2e in
    begin match s2e.sexp2_node with
      | SE2clo (_, s2e) -> sexp2_is_var_fun s2e
      | SE2fun (_, _, _, s2e) -> sexp2_is_var_res s2e
      | SE2exi (_, _, s2e) -> sexp2_is_var_fun s2e
      | SE2uni (_, _, s2e) -> sexp2_is_var_fun s2e
      | _ -> false
    end
(* end of [sexp2_is_var_fun] *)

(* ****** ****** *)

let rec sexp2_gen (stamp: stamp) (s2e0: sexp2): sexp2 =
  let s2vs_ref: svar2 list ref = ref [] in
  let rec aux s2e0 =
    let s2t0 = s2e0.sexp2_sort in
    let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
      | SE2app (s2e1, s2es2) -> begin
	let s2e1 = aux s2e1 in let s2es2 = aux_list s2es2 in
	  match s2e1.sexp2_node with
	    | SE2lam (s2vs, body) ->
		let sub = sexp2_list_bind Loc.nonloc s2vs s2es2 in
		let body = sexp2_subst sub body in aux body
	    | _ -> sexp2_app_with_sort s2t0 s2e1 s2es2
	end
      | SE2clo (knd, s2e) ->
	  let s2e = aux s2e in sexp2_clo_with_sort s2t0 knd s2e
      | SE2exi (s2vs, s2ps, s2e) -> aux_exi s2vs s2ps s2e
      | SE2fun (lin, sf2e, (npf, s2es), s2e) ->
	  let s2es = aux_list s2es and s2e = aux s2e in
	    sexp2_fun_with_sort s2t0 lin sf2e (npf, s2es) s2e
      | SE2mfun (_, s2es, s2e) -> sexp2_mfun None s2es s2e
      | SE2tyrec (stamp, (npf, ls2es)) ->
	  let ls2es = aux_lablist ls2es in
	    sexp2_tyrec_with_sort s2t0 stamp npf ls2es
      | SE2uni (s2vs, s2ps, s2e) ->
	  let s2ps = aux_list s2ps in let s2e = aux s2e in
	    sexp2_uni s2vs s2ps s2e
      | SE2union (s2i, ls2es) ->
	  let s2i = aux s2i in let ls2es = aux_lablist ls2es in
	    sexp2_union_with_sort s2t0 s2i ls2es
      | _ -> s2e0

  and aux_list s2es = List.map aux s2es
  and aux_lablist ls2es =
    List.map (function (l, s2e) -> (l, aux s2e)) ls2es

  and aux_exi s2vs s2ps s2e = match s2vs with
    | [s2v0] when svar2_is_unsorted s2v0 -> begin
	let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
	  | SE2VarApp (s2V, arg) ->
	      if Stamps.mem stamp s2V.sVar2_svs then
		let () = srt2_solve s2V.sVar2_arg_sort srt2_unit in
		let s2t_res = s2e.sexp2_sort in
		let s2t_fun = srt2_fun [srt2_unit] s2t_res in
		let s2e_body =
		  let s2v = svar2_new s2t_res in
		  let () = s2vs_ref := s2v :: !s2vs_ref in
		    sexp2_var s2v in
		let () =
		  let s2v = svar2_new srt2_unit in
		  let s2e_lam = sexp2_lam_with_sort s2t_fun [s2v] s2e_body in
		    s2V.sVar2_link <- Some s2e_lam in
		  s2e_body
	      else sexp2_exi s2vs s2ps s2e
	  | _ -> begin
	      P.eprintf "sexp2_gen: aux_exi: %a\n" fprint_sexp2 s2e;
	      Err.abort ();
	    end
      end
    | [s2v0] when svar2_is_unisorted s2v0 -> aux s2e
    | _ -> sexp2_exi s2vs (aux_list s2ps) (aux s2e) in

  let s2e0 = aux s2e0 in sexp2_uni (List.rev !s2vs_ref) [] s2e0
(* end of [sexp2_gen] *)

(* ****** ****** *)

let rec skexp2_match (sk1: skexp2) (sk2: skexp2): bool =
(*
  let () =
    P.fprintf stdout "skexp2_match: sk1 = %a and sk2 = %a\n"
      fprint_skexp2 sk1 fprint_skexp2 sk2 in
*)
  match sk1, sk2 with
    | SKE2bot, _ -> true
    | _, SKE2bot -> true
    | SKE2app (sk11, sks12), SKE2app (sk21, sks22) ->
	(skexp2_match sk11 sk21) && (skexp2_list_match sks12 sks22)
    | SKE2cst s2c1, SKE2cst s2c2 -> scst2_leq s2c2 s2c1
    | SKE2fun (sks11, sk12), SKE2fun (sks21, sk22) ->
	(skexp2_list_match sks21 sks11) && (skexp2_match sk12 sk22)
    | SKE2tyarr, SKE2tyarr -> true
    | SKE2tyrec (k1, lsks1), SKE2tyrec (k2, lsks2) ->
	tyrec_kind_eq k1 k2 && labskexp2_list_match lsks1 lsks2
    | SKE2var s2v1, SKE2var s2v2 -> svar2_eq s2v1 s2v2
    | _, _ -> false
(* end of [skexp2_match] *)

and skexp2_list_match (sks1: skexp2 list) (sks2: skexp2 list): bool =
  match sks1, sks2 with
    | [], [] -> true
    | sk1 :: sks1, sk2 :: sks2 ->
	skexp2_match sk1 sk2 && skexp2_list_match sks1 sks2
    | _, _ -> false
(* end of [skexp2_list_match] *)

and labskexp2_list_match
  (lsks1: labskexp2 list) (lsks2: labskexp2 list): bool =
  match lsks1, lsks2 with
    | [], [] -> true
    | (l1, sk1) :: lsks1, (l2, sk2) :: lsks2 ->
	Lab.eq l1 l2 &&	skexp2_match sk1 sk2 && labskexp2_list_match lsks1 lsks2
    | _, _ -> false
(* end of [labskexp2_list_match] *)

(* ****** ****** *)

let skexp2_match_args (sk1: skexp2) (sks2: skexp2 list)
  : (skexp2 list * skexp2) option =
  match sk1 with
    | SKE2fun (sks11, sk12) ->
	if skexp2_list_match sks11 sks2 then Some (sks11, sk12) else None
    | _ -> None
(* end of [skexp2_match_args] *)

(* ****** ****** *)

let rec skexp2_leq (sk1: skexp2) (sk2: skexp2): bool =
  match sk1, sk2 with
    | _, SKE2bot -> true
    | SKE2app (sk11, sks12), SKE2app (sk21, sks22) ->
	(skexp2_leq sk11 sk21) && (skexp2_list_leq sks12 sks22)
    | SKE2cst s2c1, SKE2cst s2c2 -> scst2_leq s2c1 s2c2
    | SKE2fun (sks11, sk12), SKE2fun (sks21, sk22) ->
	(skexp2_list_leq sks21 sks11) && (skexp2_leq sk12 sk22)
    | SKE2tyarr, SKE2tyarr -> true
    | SKE2tyrec (k1, lsks1), SKE2tyrec (k2, lsks2) ->
	tyrec_kind_eq k1 k2 && labskexp2_list_leq lsks1 lsks2
    | SKE2var s2v1, SKE2var s2v2 -> svar2_eq s2v1 s2v2
    | _, _ -> false
(* end of [skexp2_leq] *)

and skexp2_list_leq (sks1: skexp2 list) (sks2: skexp2 list): bool =
  match sks1, sks2 with
    | [], [] -> true
    | sk1 :: sks1, sk2 :: sks2 ->
	skexp2_leq sk1 sk2 && skexp2_list_leq sks1 sks2
    | _, _ -> false
(* end of [skexp2_list_leq] *)

and labskexp2_list_leq
  (lsks1: labskexp2 list) (lsks2: labskexp2 list): bool =
  match lsks1, lsks2 with
    | [], [] -> true
    | (l1, sk1) :: lsks1, (l2, sk2) :: lsks2 ->
	Lab.eq l1 l2 &&	skexp2_leq sk1 sk2 && labskexp2_list_leq lsks1 lsks2
    | _, _ -> false
(* end of [labskexp2_list_leq] *)

let rec skexp2_list_list_leq skss1 skss2 =
  match skss1, skss2 with
    | [], [] -> true
    | sks1 :: skss1, sks2 :: skss2 ->
	skexp2_list_leq sks1 sks2 && skexp2_list_list_leq skss1 skss2
    | _, _ -> false
(* end of [skexp2_list_list_leq] *)

(* ****** ****** *)

let skexp2_min loc sk0 (sks: skexp2 list): skexp2 =
  let rec aux sk0 sks = match sks with
    | [] -> sk0
    | sk :: sks ->
	if skexp2_leq sk0 sk then aux sk0 sks
	else if skexp2_leq sk sk0 then aux sk sks
	else begin
	  P.eprintf "%a: skexp2_min: aux: %a <> %a\n"
	    Loc.fprint loc fprint_skexp2 sk0 fprint_skexp2 sk;
	  Err.abort ()
	end in
    aux sk0 sks
(* end of [skexp2_min] *)

let rec skexp2_of_sexp2 (s2e: sexp2): skexp2 =
  let fvs = sexp2_fvs_0 s2e in
  let rec aux s2e =
    let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
      | SE2app (s2e, s2es) -> begin
	  let sk = aux s2e and sks = aux_arg_list s2es in
	    match sks with [] -> sk | _ :: _ -> SKE2app (sk, sks)
	end
      | SE2clo (knd, s2e) -> SKE2clo (knd, aux s2e)
      | SE2cst s2c -> SKE2cst s2c
      | SE2exi (_, _, s2e) -> aux s2e
      | SE2fun (_, _, (npf, s2es), s2e) ->
	  let sks = aux_list s2es and sk = aux s2e in SKE2fun (sks, sk)
      | SE2refarg (_(*refval*), s2e_arg, _(*s2e_res*)) -> aux s2e_arg
      | SE2tyarr _ -> SKE2tyarr
      | SE2tyrec (k, (npf, ls2es)) ->
	  let lsks = aux_lablist ls2es in SKE2tyrec (k, lsks)
      | SE2uni (_, _, s2e) -> aux s2e
      | SE2var s2v ->
	  if Stamps.mem s2v.svar2_stamp fvs then SKE2var s2v else SKE2bot
      | SE2Var s2V -> aux_sVar2 s2V
      | _ -> SKE2bot

  and aux_list s2es = List.map aux s2es
  and aux_lablist ls2es = List.map (function (l, s2e) -> (l, aux s2e)) ls2es

  and aux_arg_list = function
    | s2e :: s2es -> begin
	let sks = aux_arg_list s2es in
	  if sexp2_is_impredicative s2e then aux s2e :: sks else sks
      end
    | [] -> []

  and aux_sVar2 s2V = match s2V.sVar2_link with
    | Some s2e -> aux s2e
    | None -> begin
	let sk = skexp2_min s2V.sVar2_loc SKE2bot (aux_list s2V.sVar2_lbs) in
	  skexp2_min s2V.sVar2_loc sk (aux_list s2V.sVar2_ubs)
      end in
    aux s2e
(* end of [skexp2_of_sexp2] *)

(* ****** ****** *)

let sexp2_list_list_btw_int_int_int_bool
  (s2ess_ind: sexp2 list list) (s2ess_dim: sexp2 list list)
  : (sexp2 list) option =
  let aux s2ps s2e_ind s2e_dim =
    let s2es_arg = [sexp2_intinf_zero; s2e_ind; s2e_dim] in
    let s2p = Btw_int_int_int_bool.make_exp (Some s2es_arg) in
      s2p :: s2ps in
  let rec aux_list s2ps s2es_ind s2es_dim =
    match s2es_ind, s2es_dim with
      | [], [] -> Some s2ps
      | s2e_ind :: s2es_ind, s2e_dim :: s2es_dim ->
	  let s2ps = aux s2ps s2e_ind s2e_dim in
	    aux_list s2ps s2es_ind s2es_dim
      | _, _ -> None in
  let rec aux_list_list s2ps s2ess_ind s2ess_dim =
    match s2ess_ind, s2ess_dim with
      | [], [] -> Some s2ps
      | s2es_ind :: s2ess_ind, s2es_dim :: s2ess_dim -> begin
	  match aux_list s2ps s2es_ind s2es_dim with
	    | None -> None
	    | Some s2ps -> aux_list_list s2ps s2ess_ind s2ess_dim
	end
      | _, _ -> None in
    aux_list_list [] s2ess_ind s2ess_dim
(* end of [sexp2_list_list_btw_int_int_int_bool] *)

let sexp2_select_get_ind loc0
  (s2e_arr: sexp2) (s2ess_ind: sexp2 list list)
  : sexp2 (* type *) * sexp2 list (* constraints *) =
  let s2e_arr = sexp2_whnf s2e_arr in match s2e_arr.sexp2_node with
    | SE2tyarr (s2e_elt, s2ess_dim) -> begin
	match sexp2_list_list_btw_int_int_int_bool s2ess_ind s2ess_dim with
	  | Some s2ps -> (s2e_elt, s2ps)
	  | None -> begin
	      P.eprintf
		"%a: sexp2_select_get_ind: array dimension mismatch: %a\n"
		Loc.fprint loc0 fprint_sexp2 s2e_arr;
	      Err.abort ();
	    end
      end
    | _ -> begin
	P.eprintf
	  "%a: sexp2_select_get_ind: not an array type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e_arr;
	Err.abort ();
      end
(* end of [sexp2_select_get_ind] *)

(* ****** ****** *)

let sexp2_select_get_lab loc0 (s2e0: sexp2) (l0: lab)
  : sexp2 (* type *) * sexp2 option (* constraint *) =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
(*
    | SE2datcon (d2c, s2ls_arg) -> begin
	let os2e = match Lab.int_of l0 with
	  | Some n -> begin match list_nth s2ls_arg n with
	      | Some s2l -> Some (sexp2_ptr_addr_type s2l)
	      | None -> None
	    end
	  | None -> None in
	let s2e = match os2e with
	  | Some s2e -> s2e
	  | None -> begin
	      P.eprintf
		"%a: sexp2_select_get_lab: the label <%a> is not found.\n"
		Loc.fprint loc0 Lab.fprint l0;
	      Err.abort ()
	    end in
	  (s2e, None)
      end
*)
    | SE2tyrec (stamp, (npf, ls2es)) -> begin
	match labsexp2_list_select_get ls2es l0 with
	  | Some (i, s2e) -> (s2e, None)
	  | None -> begin
	      P.eprintf
		"%a: sexp2_select_get_lab: the label <%a> is not found in {%a}.\n"
		Loc.fprint loc0 Lab.fprint l0 fprint_labsexp2_list ls2es;
	      Err.abort ();
	    end
      end
    | SE2union (s2i, ls2es) -> begin
	match labsexp2_list_select_get ls2es l0 with
	  | Some (i, s2e) ->
	      if sexp2_is_intinf_zero s2i then (sexp2_top s2e, None)
	      else let s2p = sexp2_eqeq s2i (sexp2_int (i+1)) in
		(s2e, Some s2p)
	  | None -> begin
	      P.eprintf
		"%a: sexp2_select_get_lab: the label <%a> is not found in {%a}.\n"
		Loc.fprint loc0 Lab.fprint l0 fprint_labsexp2_list ls2es;
	      Err.abort ();
	    end
      end
    | _ -> begin
	P.eprintf
	  "%a: sexp2_select_get_lab: not a struct or union type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e0;
	Err.abort ();
      end
(* end of [sexp2_select_get_lab] *)

let sexp2_select_get loc0 (s2e0: sexp2) (s2lab0: slab2)
  : sexp2 (* type *) *
    bool (* array selection *) *
    sexp2 list (* constraint *) *
    slab2 =
  match s2lab0 with
    | SL2lab0 l ->
	let (s2e_itm, os2p) = sexp2_select_get_lab loc0 s2e0 l in
	let s2ps = match os2p with None -> [] | Some s2p -> [s2p] in
	  (s2e_itm, false, s2ps, slab2_lab1 l s2e0)
    | SL2lab1 (l, _) ->
	let (s2e_itm, os2p) = sexp2_select_get_lab loc0 s2e0 l in
	let s2ps = match os2p with None -> [] | Some s2p -> [s2p] in
	  (s2e_itm, false, s2ps, s2lab0)
    | SL2ind0 s2ess_ind ->
	let (s2e_elt, s2ps) = sexp2_select_get_ind loc0 s2e0 s2ess_ind in
	  (s2e_elt, true, s2ps, slab2_ind1 s2ess_ind s2e_elt)
    | SL2ind1 (s2ess_ind, _) ->
	let (s2e_elt, s2ps) = sexp2_select_get_ind loc0 s2e0 s2ess_ind in
	  (s2e_elt, true, s2ps, s2lab0)
(* end of [sexp2_select_get] *)

(* ****** ****** *)

let sexp2_select_set_lab loc0
  (s2e0: sexp2) (l0: lab) (s2e_new: sexp2): sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
(*
    | SE2datcon _ -> s2e0
*)
    | SE2tyrec (k, (npf, ls2es)) -> begin
	match labsexp2_list_select_set ls2es l0 s2e_new with
	  | Some (i, ls2es) -> begin match k with
	      | TYRECbox ->
		  let s2t0 = s2e0.sexp2_sort in
		    sexp2_tyrec_with_sort s2t0 k npf ls2es
	      | _ -> sexp2_tyrec k npf ls2es
	    end
	  | None -> begin
	      P.eprintf
		"%a: sexp2_select_set_lab: the label <%a> is not found.\n"
		Loc.fprint loc0 Lab.fprint l0;
	      Err.abort ();
	    end
      end
    | SE2union (s2i, ls2es) -> begin
	match labsexp2_list_select_set ls2es l0 s2e_new with
	  | Some (i, ls2es) -> begin
	      let s2t0 = s2e0.sexp2_sort in
		sexp2_union_with_sort s2t0 (sexp2_int (i+1)) ls2es
	    end
	  | None -> begin
	      P.eprintf
		"%a: sexp2_select_set_lab: the label <%a> is not found.\n"
		Loc.fprint loc0 Lab.fprint l0;
	      Err.abort ();
	    end
      end
    | _ -> begin
	P.eprintf
	  "%a: sexp2_select_set_lab: not a struct or union type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e0;
	Err.abort ();
      end
(* end of [sexp2_select_set_lab] *)

let sexp2_select_set loc0
  (s2e0: sexp2) (s2lab0: slab2) (s2e_new: sexp2): sexp2 =
  match s2lab0 with
    | SL2lab1 (l, _) -> sexp2_select_set_lab loc0 s2e0 l s2e_new
    | _ -> error_of_deadcode "ats_stacst2: sexp2_select_set"
(* end of [sexp2_select_set] *)

(* ****** ****** *)

let rec sexp2_select_list_probe loc0 (s2e0: sexp2) (s2labs: slab2 list)
  : sexp2 list (* cstr *) * slab2 list (* typed labels *) =
  let rec aux (s2e: sexp2) s2labs = match s2labs with
    | s2lab :: s2labs -> begin
	let (s2e1, is_sub1, s2ps1, s2lab1) = sexp2_select_get loc0 s2e s2lab in
	let (s2ps, s2labs) = aux s2e1 s2labs in
	  (s2ps1 @ s2ps, s2lab1 :: s2labs)
      end
    | [] -> ([], []) in
    aux s2e0 s2labs
(* end of [sexp2_select_list_probe] *)

let rec sexp2_select_list_get loc0 (s2e0: sexp2) (s2labs: slab2 list)
  : sexp2 (* type/whole *) *
    sexp2 (* type/part *) *
    sexp2 list (* cstr *) *
    slab2 list (* typed labels *) =
(*
  let () =
    P.fprintf stdout "sexp2_select_list_get: s2e0 = %a\n"
      fprint_sexp2 s2e0 in
  let () =
    P.fprintf stdout "sexp2_select_list_get: ls = %a\n"
      Lab.fprint_list ls in
*)
  let rec aux is_sub (s2e: sexp2) s2labs = match s2labs with
    | s2lab :: s2labs -> begin
	let (s2e1, is_sub1, s2ps1, s2lab1) = sexp2_select_get loc0 s2e s2lab in
	let is_sub = is_sub || is_sub1 in
	let (s2e1, s2e_itm, s2ps, s2labs) = aux is_sub s2e1 s2labs in
	let s2e =
	  if is_sub then s2e else
	    sexp2_select_set loc0 s2e s2lab1 s2e1 in
	  (s2e, s2e_itm, s2ps1 @ s2ps, s2lab1 :: s2labs)
      end
    | [] -> begin
	if not (sexp2_is_linear s2e) then (s2e, s2e, [], [])
	else if not (is_sub) then (sexp2_top s2e, s2e, [], [])
	else begin
	  P.eprintf
	    "%a: sexp2_select_list_get: linear array selection.\n"
	    Loc.fprint loc0;
	  Err.abort ();
	end
      end in
    aux false s2e0 s2labs
(* end of [sexp2_select_list_get] *)

let sexp2_select_list_set
  loc0 (s2e0: sexp2) (s2labs: slab2 list) (s2e_new: sexp2)
  : sexp2 (* type/whole *) *
    sexp2 (* type/part *) *
    sexp2 list (* cstr *) *
    slab2 list (* typed labels *) =
  let rec aux (s2e: sexp2) s2labs = match s2labs with
    | [] -> (s2e_new, s2e, [], [])
    | s2lab :: s2labs ->
	let (s2e1, is_sub1, s2ps1, s2lab1) = sexp2_select_get loc0 s2e s2lab in
	let (s2e1, s2e_old, s2ps, s2labs) = aux s2e1 s2labs in
	let s2e1 = sexp2_select_set loc0 s2e s2lab1 s2e1 in
	  (s2e1, s2e_old, s2ps1 @ s2ps, s2lab1 :: s2labs) in
    aux s2e0 s2labs
(* end of [sexp2_select_list_set] *)

let sexp2_select_list_del loc0 (s2e0: sexp2) (s2labs: slab2 list)
  : sexp2 (* type/whole *) *
    sexp2 (* type/part *) *
    sexp2 list (* cstr *) *
    slab2 list (* typed labels *) =
  let rec aux (s2e: sexp2) (s2labs: slab2 list) = match s2labs with
    | [] -> begin
	let s2e_out = sexp2_out s2e in (s2e_out, s2e, [], [])
      end
    | s2lab :: s2labs -> begin
	let (s2e1, is_sub1, s2ps1, s2lab1) = sexp2_select_get loc0 s2e s2lab in
	let (s2e1, s2e_old, s2ps, s2labs) = aux s2e1 s2labs in
	let s2e1 = sexp2_select_set loc0 s2e s2lab1 s2e1 in
	  (s2e1, s2e_old, s2ps1 @ s2ps, s2lab1 :: s2labs)
      end in
    aux s2e0 s2labs
(* end of [sexp2_select_list_del] *)

(* ****** ****** *)

let rec sexp2_prenex (is_exi: bool) (s2e0: sexp2)
  : svar2 list * sexp2 list * sexp2 =
  let s2e0 = sexp2_whnf s2e0 in match s2e0.sexp2_node with
(*
    | SE2Var s2V -> begin
        P.eprintf "sexp2_prenex: SE2Var: s2V = %a\n" fprint_sVar2 s2V;
        Err.abort ();
      end
*)
    | SE2app (s2e_fun, s2es_arg)
	when At_viewt0ype_addr_view.eq_exp s2e_fun ->
	begin match s2es_arg with
	  | [s2e_at; s2l] ->
	      let (s2vs, s2ps, s2e_at) = sexp2_prenex is_exi s2e_at in
	      let s2e = sexp2_app_with_sort srt2_view s2e_fun [s2e_at; s2l] in
		(s2vs, s2ps, s2e)
	  | _ -> error_of_deadcode "ats_stacst2: sexp2_prenex"
	end
    | SE2exi (s2vs, s2ps, s2e) -> 
	if is_exi then sexp2_prenex_aux true s2vs s2ps s2e else ([], [], s2e0)
    | SE2tyrec (stamp, (npf, ls2es)) ->
	let (s2vs, s2ps, ls2es) = labsexp2_list_prenex is_exi ls2es in
	  (s2vs, s2ps, sexp2_tyrec_with_sort s2e0.sexp2_sort stamp npf ls2es)
    | SE2uni (s2vs, s2ps, s2e) ->
	if is_exi then ([], [], s2e0) else sexp2_prenex_aux false s2vs s2ps s2e
    | _ -> ([], [], s2e0)
(* end of [sexp2_prenex] *)

and sexp2_prenex_aux (is_exi: bool)
  (s2vs: svar2 list) (s2ps: sexp2 list) (s2e: sexp2)
  : svar2 list * sexp2 list * sexp2 =
  let (sub, s2vs) = subst_extend [] s2vs in
  let s2ps = sexp2_list_subst sub s2ps in
  let s2e = sexp2_subst sub s2e in
  let (s2vs', s2ps', s2e) = sexp2_prenex is_exi s2e in
    (s2vs @ s2vs', s2ps @ s2ps', s2e)
(* end of [sexp2_prenex_aux] *)

and sexp2_list_prenex (is_exi: bool)
  (s2es: sexp2 list): svar2 list * sexp2 list * sexp2 list =
  match s2es with
    | [] -> ([], [], [])
    | s2e :: s2es ->
	let (s2vs', s2ps', s2e) = sexp2_prenex is_exi s2e in
	let (s2vs'', s2ps'', s2es) = sexp2_list_prenex is_exi s2es in
	  (s2vs' @ s2vs'', s2ps' @ s2ps'', s2e :: s2es)
(* end of [sexp2_list_prenex] *)

and labsexp2_list_prenex (is_exi: bool) (ls2es: labsexp2 list)
  : svar2 list * sexp2 list * labsexp2 list =
  match ls2es with
    | [] -> ([], [], [])
    | (l, s2e) :: ls2es ->
	let (s2vs', s2ps', s2e) = sexp2_prenex is_exi s2e in
	let (s2vs'', s2ps'', ls2es) = labsexp2_list_prenex is_exi ls2es in
	  (s2vs' @ s2vs'', s2ps' @ s2ps'', (l, s2e) :: ls2es)
(* end of [labsexp2_list_prenex] *)

let sexp2_abstract
  (s2e: sexp2): svar2 list * sexp2 list * sexp2 =
  sexp2_prenex false s2e

let sexp2_list_abstract
  (s2es: sexp2 list): svar2 list * sexp2 list * sexp2 list =
  sexp2_list_prenex false s2es

let labsexp2_list_abstract (ls2es: labsexp2 list)
  : svar2 list * sexp2 list * labsexp2 list =
  labsexp2_list_prenex false ls2es

let sexp2_open (s2e: sexp2): svar2 list * sexp2 list * sexp2 =
  sexp2_prenex true s2e

let sexp2_list_open
  (s2es: sexp2 list): svar2 list * sexp2 list * sexp2 list =
  sexp2_list_prenex true s2es

let labsexp2_list_open (ls2es: labsexp2 list)
  : svar2 list * sexp2 list * labsexp2 list =
  labsexp2_list_prenex true ls2es

(* ****** ****** *) 

let sexp2_of_printf_c_argtype (fa: PFc.printf_c_argtype): sexp2 =
  match fa with
    | PFc.FAT_c_char -> Char_t0ype.make_exp None
    | PFc.FAT_c_double -> Double_t0ype.make_exp None
    | PFc.FAT_c_double_long -> Double_long_t0ype.make_exp None
    | PFc.FAT_c_int -> Int_t0ype.make_exp None
    | PFc.FAT_c_int_long -> Int_long_t0ype.make_exp None
    | PFc.FAT_c_int_long_long -> Int_long_long_t0ype.make_exp None
    | PFc.FAT_c_int_short -> Int_short_t0ype.make_exp None
    | PFc.FAT_c_int_short_short -> Int_short_short_t0ype.make_exp None
    | PFc.FAT_c_ptr -> Ptr_type.make_exp None
    | PFc.FAT_c_string -> String_type.make_exp None
    | PFc.FAT_c_uint -> Uint_t0ype.make_exp None
    | PFc.FAT_c_uint_long -> Uint_long_t0ype.make_exp None
    | PFc.FAT_c_uint_long_long -> Uint_long_long_t0ype.make_exp None
    | PFc.FAT_c_uint_short -> Uint_short_t0ype.make_exp None
    | PFc.FAT_c_uint_short_short -> Uint_short_short_t0ype.make_exp None
(* end of [sexp2_of_printf_c_argtype] *)

let sexp2_of_printf_c_argtypes (fas: PFc.printf_c_argtype list): sexp2 =
  let s2es_arg = List.map sexp2_of_printf_c_argtype fas in sexp2_tylst s2es_arg

(* ****** ****** *)

let rec seff2_is_nil (sf2e: seff2): bool =
  match sf2e with
    | SEFF2all -> false
    | SEFF2nil -> true
    | SEFF2set (effs, s2es) ->
	Eff.effset_is_nil effs || List.for_all sexp2_eff_is_nil s2es
(* end of [seff2_is_nil] *)

and sexp2_eff_is_nil (s2e: sexp2): bool =
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2eff sf2e -> seff2_is_nil sf2e
    | SE2var s2v -> false
    | SE2Var s2V -> begin
	P.eprintf
	  "%a: sexp2_eff_is_nil: unsolved static variable <%a>\n"
	  Loc.fprint s2V.sVar2_loc fprint_sVar2 s2V;
	Err.abort ();
      end
    | _ -> false
(* end of [sexp2_eff_is_nil] *)

(* ****** ****** *) 

let rec seff2_contain_eff (sf2e: seff2) (eff: Eff.effect): bool =
(*
  let () =
    P.fprintf stdout "seff2_contain_eff: sf2e = %a and eff= %a\n"
      fprint_seff2 sf2e Eff.fprint_effect eff in
*)
  match sf2e with
    | SEFF2all -> true
    | SEFF2nil -> false
    | SEFF2set (effs, s2es) ->
	Eff.effset_contain effs eff || sexp2_eff_list_contain_eff s2es eff
(* end of [seff2_contain_eff] *)

and sexp2_eff_contain_eff (s2e: sexp2) (eff: Eff.effect): bool =
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2eff sf2e -> seff2_contain_eff sf2e eff
    | _ -> false
(* end of [sexp2_eff_contain_eff] *)

and sexp2_eff_list_contain_eff
  (s2es: sexp2 list) (eff: Eff.effect): bool = match s2es with
    | s2e :: s2es ->
	sexp2_eff_contain_eff s2e eff || sexp2_eff_list_contain_eff s2es eff
    | [] -> false
(* end of [sexp2_eff_list_contain_eff] *)

let seff2_contain_all (sf2e: seff2): bool =
  seff2_contain_eff sf2e Syn.EFFall

let seff2_contain_effset (sf2e: seff2) (effs: Eff.effset): bool =
  Eff.effset_for_all (seff2_contain_eff sf2e) effs

(* ****** ****** *)

let rec seff2_contain_var (sf2e: seff2) (s2v: svar2): bool =
  match sf2e with
    | SEFF2all -> true
    | SEFF2nil -> false
    | SEFF2set (effs, s2es) -> sexp2_eff_list_contain_var s2es s2v
(* end of [seff2_contain_var] *)

and sexp2_eff_contain_var (s2e: sexp2) (s2v0: svar2): bool =
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2eff sf2e -> seff2_contain_var sf2e s2v0
    | SE2var s2v -> svar2_eq s2v0 s2v
    | SE2Var s2V -> begin
	P.eprintf
	  "%a: sexp2_eff_contain_var: unsolved static variable <%a>\n"
	  Loc.fprint s2V.sVar2_loc fprint_sVar2 s2V;
	Err.abort ();
      end
    | _ -> false
(* end of [sexp2_eff_contain_var] *)

and sexp2_eff_list_contain_var (s2es0: sexp2 list) (s2v: svar2): bool =
  match s2es0 with
    | s2e :: s2es ->
	sexp2_eff_contain_var s2e s2v || sexp2_eff_list_contain_var s2es s2v
    | [] -> false
(* end of [sexp2_eff_list_contain_var] *)

let rec seff2_contain_seff2 (sf2e1: seff2) (sf2e2: seff2): bool =
  match sf2e1 with
    | SEFF2all -> true
    | _ -> begin match sf2e2 with
	| SEFF2all -> seff2_contain_all sf2e1
	| SEFF2nil -> true
	| SEFF2set (effs, s2es) ->
	    seff2_contain_effset sf2e1 effs &&
	    seff2_contain_sexp2_eff_list sf2e1 s2es
      end
(* end of [seff2_contain_seff2] *)

and seff2_contain_sexp2_eff (sf2e1: seff2) (s2e2: sexp2): bool =
  let s2e2 = sexp2_whnf s2e2 in match s2e2.sexp2_node with
    | SE2eff sf2e2 -> seff2_contain_seff2 sf2e1 sf2e2
    | SE2var s2v2 -> seff2_contain_var sf2e1 s2v2
    | SE2Var s2V -> begin
	P.eprintf
	  "%a: seff2_contain_sexp2_eff: unsolved static variable <%a>\n"
	  Loc.fprint s2V.sVar2_loc fprint_sVar2 s2V;
	Err.abort ();
      end
    | _ -> false
(* end of [seff2_contain_sexp2_eff] *)

and seff2_contain_sexp2_eff_list (sf2e: seff2) (s2es: sexp2 list): bool =
  List.for_all (seff2_contain_sexp2_eff sf2e) s2es

(* ****** ****** *) 

(* end of [ats_staexp2_util.ml] *)
