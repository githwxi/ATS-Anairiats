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

module P = Printf

module Err = Ats_error
module Loc = Ats_location
module Sym = Ats_symbol
module Syn = Ats_syntax

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_effect: "; Err.error s;
end

(* ****** ****** *)

type effect = Syn.effect
type loc = Loc.location
type symbol = Sym.symbol

(* ****** ****** *)

type effset = {
  effset_exn: bool;
  effset_ntm: bool;
  effset_ref: bool;
}

let effset_iter (f: effect -> unit) (effs: effset): unit = begin
  if effs.effset_exn then f Syn.EFFexn;
  if effs.effset_ntm then f Syn.EFFntm;
  if effs.effset_ref then f Syn.EFFref;
end (* end of [effset_iter] *)

let effset_for_all (f: effect -> bool) (effs: effset): bool =
  (if effs.effset_exn then f Syn.EFFexn else true) &&
  (if effs.effset_ntm then f Syn.EFFntm else true) &&
  (if effs.effset_ref then f Syn.EFFref else true) &&
  true
(* end of [effset_for_all] *)

(* ****** ****** *)

let fprint_effset (out: out_channel) (effs: effset): unit =
  let r = ref 0 in
  let f eff =
    if !r > 0 then begin
      P.fprintf out ",%a" Syn.fprint_effect eff; r := !r+1
    end else begin
      Syn.fprint_effect out eff; r := !r+1
    end in
    effset_iter f effs
(* end of [fprint_effset] *)

(* ****** ****** *)

let effset_make
  (b_exn: bool) (b_ntm: bool) (b_ref: bool): effset = {
    effset_exn = b_exn;
    effset_ntm = b_ntm;
    effset_ref = b_ref;
  }
(* end of [effset_make] *)

let effset_all: effset = {
  effset_exn = true;
  effset_ntm = true;
  effset_ref = true;
}

let effset_nil: effset = {
  effset_exn = false;
  effset_ntm = false;
  effset_ref = false;
}

let effset_is_nil (effs: effset): bool =
  not (effs.effset_exn || effs.effset_ntm || effs.effset_ref)
(* end of [effset_is_nil] *)

(* ****** ****** *)

let effset_add (effs: effset) (eff: effect): effset =
  match eff with
    | Syn.EFFexn -> { effs with effset_exn = true }
    | Syn.EFFntm -> { effs with effset_ntm = true }
    | Syn.EFFref -> { effs with effset_ref = true }
    | _ -> error_of_deadcode "ats_effect: effset_add"
(* end of [effset_add] *)

let effset_del (effs: effset) (eff: effect): effset =
  match eff with
    | Syn.EFFexn -> { effs with effset_exn = false }
    | Syn.EFFntm -> { effs with effset_ntm = false }
    | Syn.EFFref -> { effs with effset_ref = false }
    | _ -> error_of_deadcode "ats_effect: effset_del"
(* end of [effset_del] *)

let effset_contain (effs: effset) (eff: effect): bool =
  match eff with
    | Syn.EFFexn -> effs.effset_exn
    | Syn.EFFntm -> effs.effset_ntm
    | Syn.EFFref -> effs.effset_ref
    | _ -> false
(* end of [effset_contain] *)

let effset_union (effs1: effset) (effs2: effset): effset =
  effset_make
    (effs1.effset_exn || effs2.effset_exn)
    (effs1.effset_ntm || effs2.effset_ntm)
    (effs1.effset_ref || effs2.effset_ref)
(* end of [effset_union] *)

(* ****** ****** *)

let effset_subset (effs1: effset) (effs2: effset): bool =
  (effs1.effset_exn >= effs2.effset_exn) &&
  (effs1.effset_ntm >= effs2.effset_ntm) &&
  (effs1.effset_ref >= effs2.effset_ref) &&
  true
(* end of [effset_subset] *)

(* ****** ****** *)

type effvar = Syn.sid
type effvars = effvar list

let effvars_nil: effvars = []

let fprint_effvar = Syn.fprint_sid
let fprint_effvars out effvs =
  fprint_list_with_sep fprint_effvar out effvs ","

let rec effvars_union
  (effvs10: effvars) (effvs20: effvars): effvars =
  match effvs10, effvs20 with
    | [], _ -> effvs20
    | _, [] -> effvs10
    | effv1 :: effvs1, effv2 :: effvs2 -> begin
	match compare effv1 effv2 with
	  | 0 (* eq *) -> effv1 :: effvars_union effvs1 effvs2
	  | 1 (* gt *) -> effv2 :: effvars_union effvs10 effvs2
	  | _ (* lt *) -> effv1 :: effvars_union effvs1 effvs20
      end
(* end of [effvars_union] *)

let rec effvars_add
  (effvs0: effvars) (effv0: effvar): effvars =
  match effvs0 with
    | [] -> [effv0]
    | effv :: effvs -> begin
	match compare effv0 effv with
	  | 0 (* eq *) -> effvs0
	  | 1 (* gt *) -> effv :: effvars_add effvs effv0
	  | _ (* lt *) -> effv0 :: effvs0
      end
(* end of [effvars_add] *)

let rec effvars_contain (effvs0: effvars) (effv0: effvar): bool =
  match effvs0 with
    | [] -> false
    | effv :: effvs -> begin
	match compare effv0 effv with
	  | 0 (* eq *) -> true
	  | 1 (* gt *) -> effvars_contain effvs effv0
	  | _ (* lt *) -> false
      end
(* end of [effvars_contain] *)

let rec effvars_subset
  (effvs10: effvars) (effvs20: effvars): bool =
  match effvs10, effvs20 with
    | _, [] -> true
    | [], _ -> false
    | effv1 :: effvs1, effv2 :: effvs2 -> begin
	match compare effv1 effv2 with
	  | 0 (* eq *) -> effvars_subset effvs1 effvs2
	  | 1 (* gt *) -> effvars_subset effvs10 effvs2
	  | _ (* lt *) -> false
      end
(* end of [effvars_subset] *)

(* ****** ****** *)

type effcst =
  | EFFCall
  | EFFCnil
  | EFFCset of effset * effvars

let effcst_all = EFFCall
let effcst_nil = EFFCnil

let fprint_effcst (out: out_channel) (effc: effcst): unit =
  match effc with
    | EFFCall -> P.fprintf out "all"
    | EFFCnil -> P.fprintf out "nil"
    | EFFCset (effs, effvs) ->
	P.fprintf out "%a;%a" fprint_effset effs fprint_effvars effvs
(* end of [fprint_effcst] *)

(* ****** ****** *)

let effcst_union (effc1: effcst) (effc2: effcst): effcst =
  match effc1, effc2 with
    | EFFCall, _ -> EFFCall
    | _, EFFCall -> EFFCall
    | EFFCnil, _ -> effc2
    | _, EFFCnil -> effc1
    | EFFCset (effs1, effvs1), EFFCset (effs2, effvs2) ->
	let effs = effset_union effs1 effs2 in
	let effvs = effvars_union effvs1 effvs2 in
	  EFFCset (effs, effvs)
(* end of [effcst_union] *)

let effcst_add_eff (effc: effcst) (eff: effect): effcst =
  match effc with
    | EFFCall -> EFFCall
    | EFFCnil ->
	let effs = effset_add effset_nil eff in EFFCset (effs, [])
    | EFFCset (effs, effvs) ->
	let effs = effset_add effs eff in EFFCset (effs, effvs)
(* end of [effcst_add_eff] *)

let effcst_add_var (effc: effcst) (effv: effvar): effcst =
  match effc with
    | EFFCall -> EFFCall
    | EFFCnil -> EFFCset (effset_nil, [effv])
    | EFFCset (effs, effvs) -> EFFCset (effs, effv :: effvs)
(* end of [effcst_add_var] *)

let effcst_contain_eff (effc: effcst) (eff: effect): bool =
  match effc with
    | EFFCall -> true
    | EFFCnil -> false
    | EFFCset (effs, _) -> effset_contain effs eff
(* end of [effcst_contain_eff] *)

let effcst_contain_ntm (effc: effcst): bool =
  effcst_contain_eff effc Syn.EFFntm

let effcst_contain_var
  (effc: effcst) (effv: effvar): bool = match effc with
    | EFFCall -> true
    | EFFCnil -> false
    | EFFCset (_, effvs) -> effvars_contain effvs effv
(* end of [effcst_contain_var] *)

(* ****** ****** *)

let efftags_process_aux_errmsg loc (name: string) = begin
  Printf.fprintf stderr
    "%a: unrecognized effect constant <%s>\n" Loc.fprint loc name;
  Err.abort ();
end (* end of [efftags_process_aux_errmsg] *)

let rec efftags_process_aux
  (loc: loc) (fc: Syn.funclo)
  (is_nil: bool) (is_all: bool)
  (lin: int) (prf: int)
  (effs: effset) (effvs: effvars)
  : Syn.efftags ->
      Syn.funclo * bool * bool * int(*lin*) * int(*prf*) * effset * effvars = function
  | [] -> (fc, is_nil, is_all, lin, prf, effs, effvs)
  | Syn.EFFTAGvar effv :: tags -> efftags_process_aux
      loc fc is_nil is_all lin prf effs (effv :: effvs) tags 
  | Syn.EFFTAGcst name :: tags -> begin
      if Syn.name_is_nil name then
	efftags_process_aux loc fc true false lin prf effs effvs tags
      else if Syn.name_is_all name then
	efftags_process_aux loc fc false true lin prf effs effvs tags
      else if Syn.name_is_lazy name then
        let effs = effset_all in
        let effs = effset_del effs Syn.EFFref in
	  efftags_process_aux loc fc false false lin prf effs effvs tags
      else if Syn.name_is_exn name then
	let effs = effset_add effs Syn.EFFexn in
	  efftags_process_aux loc fc false is_all lin prf effs effvs tags
      else if Syn.name_is_exnref name then
	let effs = effset_add effs Syn.EFFexn in
	let effs = effset_add effs Syn.EFFref in
	  efftags_process_aux loc fc false is_all lin prf effs effvs tags
      else if Syn.name_is_nonterm name then
	let effs = effset_add effs Syn.EFFntm in
	  efftags_process_aux loc fc false is_all lin prf effs effvs tags
      else if Syn.name_is_term name then
	let effs = effset_del effs Syn.EFFntm in
	  efftags_process_aux loc fc is_nil false lin prf effs effvs tags
      else if Syn.name_is_ref name then
	let effs = effset_add effs Syn.EFFref in
	  efftags_process_aux loc fc false is_all lin prf effs effvs tags
      else efftags_process_aux_errmsg loc name
    end
  | Syn.EFFTAGprf :: tags -> begin
      efftags_process_aux loc fc is_nil is_all lin 1(*prf*) effs effvs tags
    end
  | Syn.EFFTAGlin i :: tags -> begin
      if i > 0 then
	efftags_process_aux loc fc false true 1(*lin*) prf effs effvs tags
      else
 	efftags_process_aux loc fc is_nil is_all 1(*lin*) prf effs effvs tags
    end
  | Syn.EFFTAGfun i :: tags -> begin
      let fc = Syn.FUNCLOfun in
	if i > 0 then
	  efftags_process_aux loc fc false true lin prf effs effvs tags
	else
 	  efftags_process_aux loc fc is_nil is_all lin prf effs effvs tags
    end
  | Syn.EFFTAGclo i :: tags -> begin
      let fc = Syn.FUNCLOclo ( 0(*clo*)) in
	if i > 0 then
	  efftags_process_aux loc fc false true lin prf effs effvs tags
	else
 	  efftags_process_aux loc fc is_nil is_all lin prf effs effvs tags
    end
  | Syn.EFFTAGcloptr i :: tags -> begin
      let fc = Syn.FUNCLOclo ( 1(*cloptr*)) in
	if i > 0 then
	  efftags_process_aux loc fc false true lin prf effs effvs tags
	else
 	  efftags_process_aux loc fc is_nil is_all lin prf effs effvs tags
    end
  | Syn.EFFTAGcloref i :: tags -> begin
      let fc = Syn.FUNCLOclo (-1(*cloref*)) in
	if i > 0 then
	  efftags_process_aux loc fc false true lin prf effs effvs tags
	else
 	  efftags_process_aux loc fc is_nil is_all lin prf effs effvs tags
    end
(* end of [efftags_process_aux] *)

let efftags_process
  (loc: loc) (fc: Syn.funclo) (tags: Syn.efftags)
  : Syn.funclo * int(*lin*) * int(*prf*) * effcst =
  let effs = effset_nil and effvs = [] in
  let (fc, is_nil, is_all, lin, prf, effs, effvs) =
    efftags_process_aux loc fc
      true(*is_nil*) false(*is_all*) 0(*lin*) 0(*prf*) effs effvs tags in
  let effc =
    if is_all then EFFCall else begin
      if is_nil then begin match effvs with
	| [] -> EFFCnil | _ :: _ -> EFFCset (effs, effvs)
      end else begin
	EFFCset (effs, effvs)
      end
    end in
    (fc, lin, prf, effc)
(* end of [efftags_process] *)

(* ****** ****** *)

(* end of [ats_effect.ml] *)
