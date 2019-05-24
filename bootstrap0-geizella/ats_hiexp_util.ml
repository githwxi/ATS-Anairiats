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

(* high-level intermediate representation *)

open Ats_misc

open Ats_staexp2
open Ats_staexp2_util
open Ats_stacst2
open Ats_dynexp2
open Ats_dynexp2_util
open Ats_hiexp

module Cnt = Ats_counter
module Eff = Ats_effect
module Lab = Ats_label
module Sym = Ats_symbol
module Syn = Ats_syntax

(* ****** ****** *)

type stamp = Cnt.count

(* ****** ****** *)

let rec hityp_is_boxed (hit0: hityp): bool =
  match hit0.hityp_node with
    | HITtyrec_box _ -> true
    | HITtyrec_sin hit -> hityp_is_boxed hit
    | _ -> false

let rec hityp_funclo_get (hit0: hityp): Syn.funclo option =
  match hit0.hityp_node with
    | HITfun (fc, _, _) -> Some fc
    | HITtyrec_sin hit -> hityp_funclo_get hit
    | _ -> None

(* ****** ****** *)

let hityp_is_tyarr (hit0: hityp): bool =
  match hit0.hityp_node with
    | HITtyarr _ -> true | _ -> false
(* end of [hityp_is_tyarr] *)

let hityp_is_singular_rec (hit0: hityp): bool =
  match hit0.hityp_node with
    | HITtyrec_sin _ -> true | _ -> false

let rec hityp_is_void (hit0: hityp): bool =
  match hit0.hityp_node with
    | HITextype name -> (name = void_type_name)
    | HITtyrec_sin hit -> hityp_is_void hit
    | HITvar s2v -> begin
	if svar2_is_boxed s2v then false else true
      end
    | _ -> false

let hityp_fun_is_void (hit0: hityp): bool =
  match hit0.hityp_node with
    | HITfun (_, _, hit_res) -> hityp_is_void hit_res
    | _ -> begin
	error_of_deadcode "ats_hiexp_util: hityp_fun_is_void"
      end (* end of [_] *)
(* end of [hityp_fun_is_void] *)

(* ****** ****** *)

let hityp_is_vararg (hit0: hityp): bool =
  match hit0.hityp_node with HITvararg -> true | _ -> false

let hityp_fun_is_vararg (hit0: hityp): bool = begin
  let rec aux hit = function
    | hit :: hits -> aux hit hits | [] -> hityp_is_vararg hit in
    match hit0.hityp_node with
      | HITfun (_, hits_arg, _) ->
(*
	  let () =
	    P.fprintf stdout "hityp_fun_is_vararg: hits_arg = %a\n"
	      fprint_hityp_list hits_arg in
*)
	  begin match hits_arg with
	    | hit_arg :: hits_arg -> aux hit_arg hits_arg | [] -> false
	  end
      | _ -> begin
          P.eprintf "hityp_fun_is_vararg: hits_arg = %a\n"
	    fprint_hityp hit0;
	  Err.abort ()
        end
end (* end of [hityp_fun_is_vararg] *)

(* ****** ****** *)

let label_is_tyarr
  (hit0: hityp) (l0: lab): bool =
  let rec istyarr
    (lhits: labhityp list): bool =
    match lhits with
    | (l, hit) :: lhits ->
        if Lab.eq (l0) (l)
          then hityp_is_tyarr(hit) else istyarr (lhits)
        (* end of [if] *)
    | [] -> false in
  match hit0.hityp_node with
  | HITtyrec_box lhits -> istyarr (lhits)
  | HITtyrec_flt lhits -> istyarr (lhits)
  | _ -> false
(* end of [label_is_tyarr] *)

(* ****** ****** *)

let hipat_list_is_used (hips: hipat list): bool =
  let aux hip = match hip.hipat_node with
    | HIPany -> false
    | HIPvar (_, d2v, None) -> dvar2_is_used d2v
    | _ -> true in
    List.exists aux hips

(* ****** ****** *)

let rec hiexp_is_value (hie0: hiexp): bool =
  match hie0.hiexp_node with
    | HIEbool _ -> true
    | HIEchar _ -> true
    | HIEcon (_, _, hies) -> hiexp_list_is_value hies
    | HIEcst _ -> true
    | HIEempty -> true
    | HIEfix (_, hie) -> hiexp_is_value hie
    | HIEfloat _ -> true
    | HIElam _ -> true
    | HIElst hies -> hiexp_list_is_value hies
    | HIEint _ -> true
    | HIErec (_, _, lhies) -> labhiexp_list_is_value lhies
    | HIEseq hies -> hiexp_list_is_value hies
    | HIEstring _ -> true
    | HIEtemplate_cst _ -> true
    | HIEtemplate_var _ -> true
    | HIEvar d2v -> not (d2v.dvar2_is_fixed)
    | _ -> false

and hiexp_list_is_value (hies: hiexp list): bool =
  List.for_all hiexp_is_value hies

and labhiexp_list_is_value (lhies: labhiexp list): bool =
  List.for_all (function (l, hie) -> hiexp_is_value hie) lhies

(* ****** ****** *)

let hicla_is_bool_fst (hicl: hicla): (bool * hiexp) option =
  match hicl.hicla_pat with
    | [hip] -> begin match hip.hipat_node with
	| HIPbool b -> begin match hicl.hicla_gua with
	    | Some _ -> None | None -> Some (b, hicl.hicla_body)
	  end
	| _ -> None
      end
    | _ -> None
(* end of [hicla_is_bool_fst] *)

let hicla_is_bool_snd (hicl: hicla): hiexp option =
  match hicl.hicla_pat with
    | [hip] -> begin match hicl.hicla_gua with
	| Some _ -> None | None -> Some hicl.hicla_body
      end
    | _ -> None
(* end of [hicla_is_bool_snd] *)

let hiexp_case_if loc (hit0: hityp)
  (is_exhaustive: bool) (hies: hiexp list) (hicls: hicla list): hiexp =
  match hies, hicls with
    | [hie], [hicl1; hicl2] -> begin
	let obhie1 = hicla_is_bool_fst hicl1 in
	let ohie2 = hicla_is_bool_snd hicl2 in
	  match obhie1, ohie2 with
	    | Some (b1, hie1), Some hie2 ->
		if b1 then hiexp_if loc hit0 hie hie1 hie2
		else hiexp_if loc hit0 hie hie2 hie1
	    | _, _ -> hiexp_case loc hit0 is_exhaustive hies hicls
      end
    | _, _ -> hiexp_case loc hit0 is_exhaustive hies hicls
(* end of [hiexp_case_if] *)

(* ****** ****** *)

type hibind =
  | HIBINDnone
  | HIBINDsome_any of hiexp
  | HIBINDsome_empty of hiexp
  | HIBINDsome_var of dvar2 * hiexp

let hidec_is_singular_var (hid: hidec): hibind =
(*
  let () = P.fprintf stdout "hidec_is_singular_var\n" in
*)
  let rec aux hie_def hip =
(*
    let () = P.fprintf stdout "hidec_is_singular_var: hip = %a\n" fprint_hipat hip in
*)
    match hip.hipat_node with
    | HIPany -> HIBINDsome_any hie_def
    | HIPempty -> HIBINDsome_empty (hie_def)
    | HIPvar (_, d2v, None) -> HIBINDsome_var (d2v, hie_def)
    | HIPrec (is_flat, hit_rec, [l, hip]) ->
	if is_flat then aux hie_def hip else HIBINDnone
    | _ -> HIBINDnone in
    begin match hid.hidec_node with
      | HIDvals (_, [d]) -> aux d.hidec_val_def d.hidec_val_pat
      | _ -> HIBINDnone
    end
(* end of [hiexp_is_singular_var] *)

(* ****** ****** *)

let rec hiexp_is_empty (hie: hiexp): bool =
  match hie.hiexp_node with
    | HIEempty -> true
    | HIErec (is_flat, hit_rec, [l, hie]) ->
	if is_flat then hiexp_is_empty hie else false
    | _ -> false
(* end of [hiexp_is_empty] *)

let hiexp_seq_simplify loc (hit0: hityp) (hies: hiexp list): hiexp =
  let rec aux res hie0 = function
    | hie :: hies ->
	if hiexp_is_empty hie0 then aux res hie hies
	else aux (hie0 :: res) hie hies
    | [] -> List.rev (hie0 :: res) in
  let hies = match hies with
    | [] -> [] | hie :: hies -> aux [] hie hies in
    match hies with [hie] -> hie | _ -> hiexp_seq loc hit0 hies
(* end of [hiexp_seq_simplify] *)

(* ****** ****** *)

type hiempvar =
  | HIEMPVARnone
  | HIEMPVARsome_emp
  | HIEMPVARsome_var of dvar2

let rec hiexp_is_empvar (hie: hiexp): hiempvar =
  match hie.hiexp_node with
    | HIEempty -> HIEMPVARsome_emp
    | HIEvar d2v -> HIEMPVARsome_var d2v
    | HIErec (is_flat, hit_rec, [l, hie]) ->
	if is_flat then hiexp_is_empvar hie else HIEMPVARnone
    | _ -> HIEMPVARnone
(* end of [hiexp_is_empvar] *)

let hiexp_let_simplify loc
  (hit0: hityp) (hids0: hidec list) (hie: hiexp): hiexp =
  let aux_simplify hid hids =
    let rec aux_init hid0 = function
      | hid :: hids -> hid0 :: (aux_init hid hids)
      | [] -> [] in
    let rec aux_last hid0 = function
      | hid :: hids -> aux_last hid hids | [] -> hid0 in
    let hid_last = aux_last hid hids in
      match hiexp_is_empvar hie with
	| HIEMPVARsome_emp -> begin
	    let bind = hidec_is_singular_var hid_last in
	      match bind with
		| HIBINDsome_any hie1 ->
		    if hityp_is_void (hie1.hiexp_type) then
		      hiexp_let loc hit0 (aux_init hid hids) hie1
		    else hiexp_let loc hit0 hids0 hie
		| HIBINDsome_empty hie1 ->
		    hiexp_let loc hit0 (aux_init hid hids) hie1
		| HIBINDsome_var (_, hie1) ->
		    if hityp_is_void (hie1.hiexp_type) then
		      hiexp_let loc hit0 (aux_init hid hids) hie1
		    else hiexp_let loc hit0 hids0 hie
		| _ -> hiexp_let loc hit0 hids0 hie
	  end
	| HIEMPVARsome_var d2v2 -> begin
	    let bind = hidec_is_singular_var hid_last in
	      match bind with
		| HIBINDsome_var (d2v1, hie1) when dvar2_eq d2v1 d2v2 ->
		    hiexp_let loc hit0 (aux_init hid hids) hie1
		| _ -> hiexp_let loc hit0 hids0 hie
	  end
	| HIEMPVARnone -> hiexp_let loc hit0 hids0 hie in
    match hids0 with
      | hid :: hids -> aux_simplify hid hids | [] -> hie
(* end of [hiexp_let_simplify] *)

(* ****** ****** *)

let int_of_sexp2 (s2e: sexp2): intinf option =
  match s2e.sexp2_node with SE2int i -> Some i | _ -> None
(* end of [int_of_sexp2] *)

let int_of_sexp2_list (s2es: sexp2 list): (intinf list) option =
  let rec aux s2es = match s2es with
    | [] -> Some []
    | s2e :: s2es -> begin
	match int_of_sexp2 s2e with
	  | None -> None
	  | Some i -> begin match aux s2es with
	      | None -> None | Some is -> Some (i :: is)
	    end
      end in
    aux s2es
(* end of [int_of_sexp2_list] *)

let int_of_sexp2_list_list (s2ess: sexp2 list list)
  : (intinf list list) option =
  let rec aux s2ess = match s2ess with
    | [] -> Some []
    | s2es :: s2ess -> begin
	match int_of_sexp2_list s2es with
	  | None -> None
	  | Some is -> begin match aux s2ess with
	      | None -> None | Some iss -> Some (is :: iss)
	    end
      end in
    aux s2ess
(* end of [int_of_sexp2_list_list] *)

(* ****** ****** *)

(* end of [ats_hiexp_util.ml] *)
