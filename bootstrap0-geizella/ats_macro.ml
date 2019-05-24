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
open Ats_dynexp2

module P = Printf

module Cnt = Ats_counter
module Err = Ats_error
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol
module Syn = Ats_syntax
module SymEnv = Ats_symenv

(* ****** ****** *)

type loc = Loc.location
type symbol = Sym.symbol

(* two standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_macro: "; Err.error s;
end

let error_with_loc loc (s: string): 'a = begin
  prerr_string "ats_macro: "; Err.error_with_loc loc s;
end

(* ****** ****** *)

type value2 =
  | VAL2char of char
  | VAL2code of dexp2
  | VAL2int of Syn.intkind * intinf
  | VAL2str of string
  | VAL2var of dvar2

let dexp2_of_value2 loc (v: value2): dexp2 =
  match v with
    | VAL2char c -> dexp2_char loc c
    | VAL2code d2e -> d2e
    | VAL2int (ik, i) -> dexp2_int loc ik i
    | VAL2str s -> dexp2_string loc s
    | VAL2var d2v -> dexp2_var loc d2v

(* ****** ****** *)

module MacEnv: Map.S with type key = Cnt.count =
  Map.Make (struct type t = stamp let compare = Cnt.compare end)

type macenv_t =  value2 MacEnv.t

let macenv_empty: macenv_t = MacEnv.empty

let macenv_find (env: macenv_t) (d2v: dvar2): value2 option =
  try Some (MacEnv.find d2v.dvar2_stamp env) with Not_found -> None

(* ****** ****** *)

let code_dvar_ev loc0 (env: macenv_t) (d2v: dvar2): macenv_t * dvar2 =
  let d2v_new = dvar2_copy loc0 d2v in
  let env = MacEnv.add d2v.dvar2_stamp (VAL2var d2v_new) env in
    (env, d2v_new)

let code_dvar_list_ev loc0 (env: macenv_t) (d2vs: dvar2 list)
  : macenv_t * dvar2 list =
  let rec aux res env = function
    | [] -> (env, List.rev res)
    | d2v :: d2vs ->
	let (env, d2v) = code_dvar_ev loc0 env d2v in
	  aux (d2v :: res) env d2vs in
    aux [] env d2vs

let rec code_pat_ev loc0 (env: macenv_t) (p2t: pat2)
  : macenv_t * pat2 = match p2t.pat2_node with
    | PT2ann (p2t, s2e) ->
	let (env, p2t) = code_pat_ev loc0 env p2t in
	  (env, pat2_ann loc0 p2t s2e)

    | PT2any -> (env, p2t)

    | PT2bool _ -> (env, p2t)

    | PT2char _ -> (env, p2t)

    | PT2con (is_ref, d2c, s2vss, s2ess, s2e, (npf, p2ts)) ->
	let (env, p2ts) = code_pat_list_ev loc0 env p2ts in
	  (env, pat2_con loc0 is_ref d2c s2vss s2ess s2e (npf, p2ts))

    | PT2empty -> (env, p2t)

    | PT2exi (s2vs, p2t) ->
	let (env, p2t) = code_pat_ev loc0 env p2t in
	  (env, pat2_exi loc0 s2vs p2t)

    | PT2int _ -> (env, p2t)

    | PT2list (npf, p2ts) ->
	let (env, p2ts) = code_pat_list_ev loc0 env p2ts in
	  (env, pat2_list loc0 (npf, p2ts))

    | PT2lst p2ts ->
	let (env, p2ts) = code_pat_list_ev loc0 env p2ts in
	  (env, pat2_lst loc0 p2ts)

    | PT2rec (is_flat, is_omit, (npf, lp2ts)) ->
	let (env, lp2ts) = code_labpat_list_ev loc0 env lp2ts in
	  (env, pat2_rec loc0 is_flat is_omit npf lp2ts)

    | PT2string _ -> (env, p2t)

    | PT2var (isref, d2v, op2t) -> begin
	let (env, d2v) = code_dvar_ev loc0 env d2v in
	  match op2t with
	    | Some p2t -> begin
		let (env, p2t) = code_pat_ev loc0 env p2t in
		  (env, pat2_var_some loc0 isref d2v p2t)
	      end
	    | None -> (env, pat2_var_none loc0 isref d2v)
      end

    | PT2vbox d2v ->
	let (env, d2v) = code_dvar_ev loc0 env d2v in
	  (env, pat2_vbox loc0 d2v)	

and code_pat_list_ev loc0 (env: macenv_t) (p2ts: pat2 list)
  : macenv_t * pat2 list =
  let rec aux res env = function
    | [] -> (env, List.rev res)
    | p2t :: p2ts ->
	let (env, p2t) = code_pat_ev loc0 env p2t in
	  aux (p2t :: res) env p2ts in
    aux [] env p2ts

and code_labpat_list_ev loc0 (env: macenv_t) (lp2ts: labpat2 list)
  : macenv_t * labpat2 list =
  let rec aux res env = function
    | [] -> (env, List.rev res)
    | (l, p2t) :: lp2ts ->
	let (env, p2t) = code_pat_ev loc0 env p2t in
	  aux ((l, p2t) :: res) env lp2ts in
    aux [] env lp2ts

(* ****** ****** *)

let rec code_dexp2_ev loc0 (env: macenv_t) (d2e0: dexp2): dexp2 =
  let rec aux d2e0 = match d2e0.dexp2_node with
    | DE2ann_type (d2e, s2e) -> dexp2_ann_type loc0 (aux d2e) s2e
    | DE2ann_seff (d2e, sf2e) -> dexp2_ann_seff loc0 (aux d2e) sf2e
    | DE2ann_funclo (d2e, fc) -> dexp2_ann_funclo loc0 (aux d2e) fc
    | DE2apps (d2e, d2as) -> begin
	let d2e = aux d2e in
	  match d2e.dexp2_node with
	    | DE2mac d2m ->
		if d2m.dmac2_abbrev then code_dexp_macapp_ev loc0 env d2m d2as
		else dexp2_apps loc0 d2e (code_dexparg_list_ev loc0 env d2as)
	    | _ -> dexp2_apps loc0 d2e (code_dexparg_list_ev loc0 env d2as)
      end (* end of [DE2apps] *)
    | DE2arr (s2e, d2es) -> dexp2_arr loc0 s2e (aux_list d2es)
    | DE2arrsub (d2s_brackets, d2e_root, d2ess_ind) ->
	let d2e_root = aux d2e_root in
	let d2ess_ind = List.map aux_list d2ess_ind in
	  dexp2_arrsub loc0 d2s_brackets d2e_root d2ess_ind
    | DE2assgn (d2e1, d2e2) -> dexp2_assgn loc0 (aux d2e1) (aux d2e2)
    | DE2case (sgn, osty2, d2es, c2ls) -> begin
	let osty2 = match osty2 with
	  | None -> None | Some sty2 -> Some (aux_sty sty2) in
	let d2es = aux_list d2es in
	let c2ls = code_cla_list_ev loc0 env c2ls in
	  dexp2_case loc0 sgn osty2 d2es c2ls
      end (* end of [DE2case] *)
    | DE2char _ -> d2e0
    | DE2con (d2c, s2es, npf, d2es) -> begin
	let d2es = aux_list d2es in dexp2_con loc0 d2c s2es npf d2es
      end (* end of [DE2con] *)
    | DE2cst _ -> d2e0
    | DE2crypt (knd, d2e) -> dexp2_crypt loc0 knd (aux d2e)
    | DE2delay d2e -> dexp2_delay loc0 (aux d2e)
    | DE2dynload _ -> d2e0
    | DE2demac d2e -> dexp2_of_value2 loc0 (dexp2_ev loc0 env d2e)
    | DE2deref d2e -> dexp2_deref loc0 (aux d2e)
    | DE2effmask (eff, d2e) -> dexp2_effmask loc0 eff (aux d2e)
    | DE2empty -> d2e0
    | DE2enmac _ -> begin
	P.eprintf "%a: code_dexp2_ev: %a\n" Loc.fprint loc0 fprint_dexp2 d2e0;
	Err.abort ();
      end (* end of [DE2enmac] *)
    | DE2exi (s2as, d2e) -> let d2e = aux d2e in dexp2_exi loc0 s2as d2e
    | DE2extval _ -> d2e0
    | DE2fix (d2v, d2e) -> begin
	let (env, d2v) = code_dvar_ev loc0 env d2v in
	let d2e = code_dexp2_ev loc0 env d2e in
	  dexp2_fix loc0 d2v d2e
      end (* end of [DE2fix] *)
    | DE2float _ -> d2e0
    | DE2for (inv, (ini, test, post), body) ->
	let init = code_dexp2_ev loc0 env ini in
	let test = code_dexp2_ev loc0 env test in
	let post = code_dexp2_ev loc0 env post in
	let body = code_dexp2_ev loc0 env body in
	  dexp2_for loc0 inv init test post body
    | DE2fold (s2c, d2e) ->
	let d2e = aux d2e in dexp2_fold loc0 s2c d2e
    | DE2foldat (s2as, d2e) -> dexp2_foldat loc0 s2as (aux d2e)
    | DE2freeat (s2as, d2e) -> dexp2_freeat loc0 s2as (aux d2e)
    | DE2if (osty2, d2e1, d2e2, od2e3) -> begin
	let osty2 = match osty2 with
	  | None -> None | Some sty2 -> Some (aux_sty sty2) in
	let d2e1 = aux d2e1 in let d2e2 = aux d2e2 in
	let od2e3 = aux_opt od2e3 in
	  dexp2_if loc0 osty2 d2e1 d2e2 od2e3
      end (* end of [DE2if] *)
    | DE2int _ -> d2e0
    | DE2lam_dyn (is_lin, (npf, p2ts), d2e) -> begin
	let (env, p2ts) = code_pat_list_ev loc0 env p2ts in
	let d2e = code_dexp2_ev loc0 env d2e in
	  dexp2_lam_dyn loc0 is_lin (npf, p2ts) d2e
      end (* end of [DE2lam_dyn] *)
    | DE2lam_met (r, s2es, d2e) ->
	let d2e = aux d2e in dexp2_lam_met loc0 r s2es d2e
    | DE2lam_sta (s2vs, s2es, d2e) ->
	let d2e = aux d2e in dexp2_lam_sta loc0 s2vs s2es d2e
    | DE2lam_sta_para (s2vs, s2es, d2e) ->
	let d2e =  aux d2e in dexp2_lam_sta_para loc0 s2vs s2es d2e
    | DE2let (d2cs, d2e) -> begin
	let (env, d2cs) = code_dec2_list_ev loc0 env d2cs in
	let d2e = code_dexp2_ev loc0 env d2e in
	  dexp2_let loc0 d2cs d2e
      end (* end of [DE2let] *)
    | DE2loopexn _ -> d2e0
    | DE2lst d2es -> begin
	let d2es = aux_list d2es in dexp2_lst loc0 d2es
      end (* end of [DE2lst] *)
    | DE2mac _ -> d2e0
    | DE2mod _ -> d2e0
    | DE2ptrof d2e ->
	let d2e = aux d2e in dexp2_ptrof loc0 d2e
    | DE2raise (d2e) ->
	let d2e = aux d2e in dexp2_raise loc0 d2e
    | DE2rec (is_flat, (npf, ld2es)) -> begin
	let ld2es = aux_lablist ld2es in dexp2_rec loc0 is_flat npf ld2es
      end (* end of [DE2rec] *)
    | DE2sel (d2e, d2ls) -> begin
	let d2e = aux d2e in
	let d2ls = aux_dlab_list d2ls in dexp2_sel loc0 d2e d2ls 
      end (* end of [DE2sel] *)
    | DE2seq d2es -> dexp2_seq loc0 (aux_list d2es)
    | DE2sif (s2e1, d2e2, d2e3) -> begin
	let d2e2 = aux d2e2 in
	let d2e3 = aux d2e3 in dexp2_sif loc0 s2e1 d2e2 d2e3
      end (* end of [DE2sif] *)
    | DE2string _ -> d2e0
    | DE2struct ld2es -> begin
	let ld2es = aux_lablist ld2es in dexp2_struct loc0 ld2es
      end (* DE2struct *)
    | DE2sym _ -> d2e0
    | DE2template (d2e, s2ess) -> begin
	let d2e = aux d2e in dexp2_template loc0 d2e s2ess
      end (* end of [DE2template] *)
    | DE2top -> d2e0
    | DE2trywith (d2e, c2ls) -> begin
	let d2e = aux d2e in
	let c2ls = code_cla_list_ev loc0 env c2ls in
	  dexp2_trywith loc0 d2e c2ls
      end (* end of [DE2trywith] *)
    | DE2var d2v -> aux_var d2v
    | DE2viewat d2e -> dexp2_viewat loc0 (aux d2e)
    | DE2unfold (s2c, d2e) -> begin
	let d2e = aux d2e in dexp2_unfold loc0 s2c d2e
      end (* end of [DE2unfold] *)
    | DE2while (inv, test, body) -> begin
	let test = code_dexp2_ev loc0 env test in
	let body = code_dexp2_ev loc0 env body in
	  dexp2_while loc0 inv test body
      end (* end of [DE2while] *)
(*
**
** Note that the variable is escaped automatically if it is bound
** So the syntax [x] in code is equivalent to [,(x)] if [x] is a
** variable.
**
*)

  and aux_var (d2v0: dvar2): dexp2 = begin 
    match macenv_find env d2v0 with
      | None -> dexp2_var loc0 d2v0 | Some v -> dexp2_of_value2 loc0 v
  end (* end of [aux_var] *)

  and aux_list (d2es0: dexp2 list): dexp2 list =
    List.map aux d2es0

  and aux_list_list
    (d2ess0: dexp2 list list): dexp2 list list =
    List.map aux_list d2ess0

  and aux_lablist
    (ld2es0: labdexp2 list): labdexp2 list =
    List.map (function (l, d2e) -> (l, aux d2e)) ld2es0

  and aux_opt (od2e0: dexp2 option): dexp2 option = begin
    match od2e0 with None -> None | Some d2e -> Some (aux d2e)
  end (* end of [aux_opt] *)

  and aux_dlab (d2l0: dlab2): dlab2 = match d2l0.dlab2_ind with
    | None -> d2l0 | Some d2ess -> {
	dlab2_lab= d2l0.dlab2_lab;
	dlab2_ind= Some (aux_list_list d2ess)
      }
  (* end of [aux_dlab] *)

  and aux_dlab_list (d2ls0: dlab2 list): dlab2 list =
    List.map aux_dlab d2ls0

  and aux_sty (sty2: statype2): statype2 = begin
    P.eprintf "%a: code_dexp2_ev: aux_sty: state type is not supported.\n"
      Loc.fprint loc0;
    Err.abort ();
  end (* end of [aux_sty] *)

  in aux d2e0
(* end of [code_dexp_ev] *)

and code_dexp_list_ev loc0
  (env: macenv_t) (d2es: dexp2 list): dexp2 list =
  List.map (code_dexp2_ev loc0 env) d2es

and code_dexp_opt_ev loc0
  (env: macenv_t) (od2e: dexp2 option): dexp2 option =
  match od2e with
    | None -> None | Some d2e -> Some (code_dexp2_ev loc0 env d2e)
(* end of [code_dexp_opt_ev] *)

and code_dexparg_ev loc0
  (env: macenv_t) (d2a: dexparg2): dexparg2 =
  match d2a with
    | DEXPARG2sta _ -> d2a
    | DEXPARG2dyn (npf, d2es) -> begin
	let d2es = code_dexp_list_ev loc0 env d2es in DEXPARG2dyn (npf, d2es)
      end
(* end of [code_dexparg_ev] *)

and code_dexparg_list_ev loc0
  (env: macenv_t) (d2as: dexparg2 list): dexparg2 list =
  List.map (code_dexparg_ev loc0 env) d2as
(* end of [code_dexparg_list_ev] *)

and code_cla_ev loc0
  (env: macenv_t) (c2l: cla2): cla2 =
  let (env, p2ts) =
    code_pat_list_ev loc0 env (c2l.cla2_pat) in
  let d2e = code_dexp2_ev loc0 env (c2l.cla2_body) in
    { c2l with cla2_pat = p2ts; cla2_body = d2e }
(* end of [code_cla_ev] *)

and code_cla_list_ev loc0 (env: macenv_t) (c2ls: cla2 list)
  : cla2 list = List.map (code_cla_ev loc0 env) c2ls

(* ****** ****** *)

and code_dexp_macapp_ev loc0
  (env: macenv_t) (d2m: dmac2) (d2as: dexparg2 list): dexp2 =
  let (d2as1, d2as2) =
    let rec aux res d2as n =
      if n > 0 then
	match d2as with
	  | [] -> begin
	      P.eprintf "%a: too few arguments for <%a>.\n"
		Loc.fprint loc0 fprint_dmac2 d2m;
	      Err.abort ();
	    end
	  | d2a :: d2as -> aux (d2a :: res) d2as (n-1)
      else (List.rev res, d2as) in
      aux [] d2as (List.length d2m.dmac2_arity) in
  let vss =
    let aux d2a = match d2a with
      | DEXPARG2dyn (npf, d2es) ->
	  let f d2e = VAL2code (code_dexp2_ev loc0 env d2e) in
	    List.map f d2es
      | DEXPARG2sta _ -> begin
	  P.eprintf "%a: illegal static macro application.\n"
	    Loc.fprint loc0;
	  Err.abort ();
	end in
      List.map aux d2as1 in
  let d2e = dexp2_of_value2 loc0 (dexp_apps_ev loc0 env d2m vss) in
    match d2as2 with [] -> d2e | _ -> dexp2_apps loc0 d2e d2as2
(* end of [code_dexp_macapp_ev] *)

(* ****** ****** *)

and code_dec2_ev loc0 (env: macenv_t) (d2c: dec2): macenv_t * dec2 =
  match d2c.dec2_node with
    | DC2funs (is_temp, fk, ds) ->
	let (env, ds) = code_dec2_fun_list_ev loc0 env ds in
	let d2c = dec2_funs loc0 is_temp fk ds in
	  (env, d2c)
    | DC2vals (vk, ds) ->
	let (env, ds) = code_dec2_val_list_ev loc0 env ds in
	let d2c = dec2_vals loc0 vk ds in
	  (env, d2c)
    | DC2valrecs ds ->
	let (env, ds) = code_dec2_val_list_ev loc0 env ds in
	let d2c = dec2_valrecs loc0 ds in
	  (env, d2c)
    | DC2vars (is_stack, ds) ->
	let (env, ds) = code_dec2_var_list_ev loc0 env ds in
	let d2c = dec2_vars loc0 is_stack ds in
	  (env, d2c)
    | DC2local _ -> error_with_loc loc0 "code_dec2_ev: DC2local"
    | DC2impls ds ->
	let ds = code_dec2_impl_list_ev loc0 env ds in
	let d2c = dec2_impls loc0 ds in
	  (env, d2c)
    | _ -> (env, d2c)
(* end of [code_dec2_ev] *)

and code_dec2_fun_list_ev loc0 (env: macenv_t) (ds: dec2_fun list)
  : macenv_t * dec2_fun list =
  let (env, res1) =
    let rec aux res1 env = function
      | [] -> (env, res1)
      | d :: ds ->
	  let (env, d2v) = code_dvar_ev loc0 env d.dec2_fun_name in
	    aux ((d2v, d) :: res1) env ds in
      aux [] env ds in
  let ds =
    let rec aux res2 = function
      | [] -> res2
      | (d2v, d) :: rest ->
	  let d2e = code_dexp2_ev loc0 env d.dec2_fun_def in
	  let d = dec2_fun loc0 d2v d2e in
	    aux (d :: res2) rest in
      aux [] res1 in
    (env, ds)
(* end of [code_dec2_fun_list_ev] *)

and code_dec2_val_list_ev loc0 (env: macenv_t) (ds: dec2_val list)
  : macenv_t * dec2_val list =
  let (env, res1) =
    let rec aux res1 env = function
      | [] -> (env, res1)
      | d :: ds ->
	  let (env, p2t) = code_pat_ev loc0 env d.dec2_val_pat in
	    aux ((p2t, d) :: res1) env ds in
      aux [] env ds in
  let ds =
    let rec aux res2 = function
      | [] -> res2
      | (p2t, d) :: rest ->
	  let d2e = code_dexp2_ev loc0 env d.dec2_val_def in
	  let d = dec2_val loc0 p2t d2e d.dec2_val_ann in
	    aux (d :: res2) rest in
      aux [] res1 in
    (env, ds)
(* end of [code_dec2_val_list_ev] *)

and code_dec2_var_list_ev loc0 (env: macenv_t) (ds: dec2_var list)
  : macenv_t * dec2_var list = error_with_loc loc0 "code_dec2_var_list_ev"
(* end of [code_dec2_var_list_ev] *)

and code_dec2_impl_list_ev loc0 (env: macenv_t) (ds: dec2_impl list)
  : dec2_impl list =
  let aux d =
    let def = code_dexp2_ev loc0 env d.dec2_impl_def in
      dec2_impl loc0 d.dec2_impl_cst d.dec2_impl_decarg d.dec2_impl_tmparg def in
    List.map aux ds
(* end of [code_dec2_impl_list_ev] *)

and code_dec2_list_ev loc0 (env: macenv_t) (d2cs: dec2 list)
  : macenv_t * dec2 list =
  let rec aux res env = function
    | [] -> (env, List.rev res)
    | d2c :: d2cs ->
	let (env, d2c) = code_dec2_ev loc0 env d2c in
	  aux (d2c :: res) env d2cs in
    aux [] env d2cs
(* end of [code_dec2_list_ev] *)

(* ****** ****** *)

and dexp2_ev loc0 (env: macenv_t) (d2e: dexp2): value2 =
  match d2e.dexp2_node with
    | DE2apps (d2e, d2as) -> begin match d2e.dexp2_node with
	| DE2mac d2m ->
	    let vss = List.map (dexparg_ev loc0 env) d2as in
	      dexp_apps_ev loc0 env d2m vss
	| _ -> begin
	    P.eprintf "%a: dexp2_ev: illegal macro application.\n"
	      Loc.fprint loc0;
	    Err.abort ();
	  end
      end

    | DE2enmac d2e -> VAL2code (code_dexp2_ev loc0 env d2e)

    | DE2mac d2m -> begin
	match d2m.dmac2_arity with
	  | [] -> VAL2code (d2m.dmac2_def)
	  | _ :: _ -> begin
	      P.eprintf "%a: the macro <%a> needs to be applied.\n"
		Loc.fprint loc0 fprint_dmac2 d2m;
	      Err.abort ();
	    end
      end

    | DE2var d2v -> begin
	match macenv_find env d2v with
	  | Some v -> v
	  | None -> begin
	      P.eprintf "%a: unrecognized identifier <%a>.\n"
		Loc.fprint loc0 fprint_dvar2 d2v;
	      Err.abort ();
	    end
      end

    | _ -> begin
	P.eprintf "%a: dexp2_ev: illegal macro expression.\n"
	  Loc.fprint loc0;
	Err.abort ();
      end
(* end of [dexp_ev] *)

and dexp_list_ev loc0
  (env: macenv_t) (d2es: dexp2 list): value2 list =
  List.map (dexp2_ev loc0 env) d2es

and dexparg_ev loc0 (env: macenv_t) (d2a: dexparg2): value2 list =
  match d2a with
    | DEXPARG2dyn (npf, d2es) -> dexp_list_ev loc0 env d2es
    | DEXPARG2sta _ -> begin
	P.eprintf "%a: dexparg_ev: illegal static macro application.\n"
	  Loc.fprint loc0;
	Err.abort ();
      end
(* end of [dexparg_ev] *)

and dexp_apps_ev loc0
  (env: macenv_t) (d2m: dmac2) (vss: value2 list list): value2 =
  let () = (* arity checking for macro application *)
    let rec aux = function
      | [], [] -> ()
      | n :: ns, vs :: vss ->
	  if n == List.length vs then aux (ns, vss)
	  else begin
	    P.eprintf "%a: arity mismatching for <%a>.\n"
	      Loc.fprint loc0 fprint_dmac2 d2m;
	    Err.abort ();
	  end
      | [], _ :: _ -> begin
	  P.eprintf "%a: too many arguments for <%a>.\n"
	    Loc.fprint loc0 fprint_dmac2 d2m;
	  Err.abort ();
	end
      | _ :: _, [] -> begin
	  P.eprintf "%a: too few arguments for <%a>.\n"
	    Loc.fprint loc0 fprint_dmac2 d2m;
	  Err.abort ();
	end in
      aux (d2m.dmac2_arity, vss) in
    dexp_mac_ev loc0 env d2m vss
(* end of [dexp_apps_ev] *)

and dexp_mac_ev loc0
  (env: macenv_t) (d2m: dmac2) (vss: (value2 list) list): value2 =
  let rec aux env d2vs vs =
    match (d2vs, vs) with
      | [], [] -> env
      | d2v :: d2vs, v :: vs ->
	  let env = MacEnv.add (d2v.dvar2_stamp) v env in
	    aux env d2vs vs
      | _, _ -> begin
	P.eprintf "%a: arity error for the macro <%a>.\n"
	  Loc.fprint loc0 fprint_dmac2 d2m;
	  Err.abort ();
	end in
  let rec aux_list env d2vss vss =
    match (d2vss, vss) with
      | d2vs :: d2vss, vs :: vss -> begin
	  let env = aux env d2vs vs in aux_list env d2vss vss
	end
      | [], [] -> env
      | _, _ -> begin
	  P.eprintf "%a: arity error for the macro <%a>.\n"
	    Loc.fprint loc0 fprint_dmac2 d2m;
	  Err.abort ();
	end in
  let env = aux_list env (d2m.dmac2_arg) vss in
    if d2m.dmac2_abbrev then
      VAL2code (code_dexp2_ev loc0 env (d2m.dmac2_def))
    else begin
      dexp2_ev loc0 env (d2m.dmac2_def)
    end
(* end of [dexp_mac_ev] *)

(* ****** ****** *)

let macro_decode_abbrev loc0
  (d2m: dmac2) (d2as: dexparg2 list): dexp2 =
  code_dexp_macapp_ev loc0 macenv_empty d2m d2as
(* end of [macro_decode_abbrev] *)

let macro_decode (d2e: dexp2): dexp2 =
  let loc = d2e.dexp2_loc in
    dexp2_of_value2 loc (dexp2_ev loc macenv_empty d2e)
(* end of [macro_decode] *)

(* ****** ****** *)

(*

let the_level: int ref = ref 0
let get_the_level (): int = !the_level
let reset_the_level (): unit = (the_level := 0)
let inc_the_level (): unit = (the_level := !the_level + 1)
let dec_the_level (): unit = (the_level := !the_level - 1)
let initialize (): unit = reset_the_level ()

*)

(* ****** ****** *)

(* end of [ats_macro.ml] *)
