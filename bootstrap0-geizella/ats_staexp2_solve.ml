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

module PR = Printf

module Cnt = Ats_counter
module Err = Ats_error
module EM3 = Ats_errmsg3
module Loc = Ats_location

module SEnv3 = Ats_staenv3

(* ****** ****** *)

type loc = Loc.location
type stamp = Cnt.count

(* a standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_staexp2_solve: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

let sexp2_head_var_test (s2e1: sexp2) (s2e2: sexp2): bool =
  match sexp2_head_var s2e1 with
    | None -> false
    | Some s2v1 -> begin match sexp2_head_var s2e2 with
	| None -> false
	| Some s2v2 -> svar2_eq s2v1 s2v2
      end
(* end of [sexp2_head_var_test] *)

(* ****** ****** *)

let clokind_equal_solve loc0
  (knd1: int) (knd2: int): unit = begin
  if knd1 <> knd2 then begin
    PR.eprintf "%a: function/closure mismatch.\n" Loc.fprint loc0;
    Err.abort ();
    end 
end (* end of [clokind_equal_solve] *)

(* ****** ****** *)

let funclo_equal_solve loc0
  (fc1: Syn.funclo) (fc2: Syn.funclo): unit = begin
  let err = match fc1, fc2 with
    | Syn.FUNCLOfun, Syn.FUNCLOfun -> 0
    | Syn.FUNCLOclo i1, Syn.FUNCLOclo i2 ->
	if i1 = i2 then 0 else 1
    | _, _ -> 1 in
    if err > 0 then begin
      PR.eprintf "%a: function/closure mismatch.\n" Loc.fprint loc0;
      Err.abort ();
    end 
end (* end of [funcloref_equal_solve] *)

(* ****** ****** *)

let funlinear_equal_solve loc0 (lin1: int) (lin2: int): unit = begin
  if lin1 = lin2 then () else begin
    PR.eprintf "%a: function linearity mismatch.\n" Loc.fprint loc0;
    Err.abort ();
  end 
end (* end of [funlinear_equal_solve] *)

(* ****** ****** *)

let pfarity_equal_solve loc0 (npf1: int) (npf2: int): unit =
(*
  let () =
    PR.fprintf stdout
      "pfarity_equal_solve: npf1 = %i and npf2 = %i\n" npf1 npf2 in
*)
  if npf1 < npf2 then begin
    PR.eprintf "%a: too few proof argumets.\n" Loc.fprint loc0;
    Err.abort ();
  end else if npf1 > npf2 then begin
    PR.eprintf "%a: too many proof argumets.\n" Loc.fprint loc0;
    Err.abort ();
  end else ()
(* end of [pfarity_equal_solve] *)

(* ****** ****** *)

let refargptr_equal_solve loc0 (ptr1: int) (ptr2: int): unit =
(*
  let () =
    PR.fprintf stdout
      "pfarity_equal_solve: ptr1 = %i and ptr2 = %i\n" ptr1 ptr2 in
*)
  if ptr1 <> ptr2 then begin
    PR.eprintf "%a: refarg style mismatch.\n" Loc.fprint loc0;
    Err.abort ();
  end else ()
(* end of [refargptr_equal_solve] *)

(* ****** ****** *)

let rec sexp2_equal_solve loc0 (s2e10: sexp2) (s2e20: sexp2): unit =
  let s2e10 = sexp2_whnf s2e10 and s2e20 = sexp2_whnf s2e20 in
(*
  let () = PR.fprintf stdout "sexp2_equal_solve:\n" in
  let () = PR.fprintf stdout "  s2e1 = %a\n" fprint_sexp2 s2e1 in
  let () = PR.fprintf stdout "  s2e2 = %a\n" fprint_sexp2 s2e2 in
*)
    match s2e10.sexp2_node, s2e20.sexp2_node with
      | SE2Var s2V1, SE2Var s2V2 ->
	  if sVar2_neq s2V1 s2V2 then
	    let svs = Stamps.inter s2V1.sVar2_svs s2V2.sVar2_svs in
	    let () = (s2V1.sVar2_svs <- svs; s2V2.sVar2_svs <- svs) in
	    let s2t1 = s2V1.sVar2_sort and s2t2 = s2V2.sVar2_sort in
	      if srt2_leq s2t2 s2t1 then
		sexp2_equal_solve_Var loc0 s2V1 s2e10 s2e20
	      else
		sexp2_equal_solve_Var loc0 s2V2 s2e20 s2e10
	  else ()
      | SE2Var s2V1, _ -> sexp2_equal_solve_Var loc0 s2V1 s2e10 s2e20
      | _, SE2Var s2V2 -> sexp2_equal_solve_Var loc0 s2V2 s2e20 s2e10

      | SE2cst s2c1, SE2cst s2c2 ->
	  if scst2_eq s2c1 s2c2 then () else begin
	    PR.eprintf "%a: sexp2_equal_solve: %a <> %a\n"
	      Loc.fprint loc0 fprint_scst2 s2c1 fprint_scst2 s2c2;
	    Err.abort ();	      
	  end

      | SE2datcon (d2c1, s2ls1), SE2datcon (d2c2, s2ls2) ->
	  if dcon2_eq d2c1 d2c2 then
	    sexp2_list_equal_solve loc0 s2ls1 s2ls2
	  else begin
	    PR.eprintf "%a: sexp2_equal_solve: %a <> %a\n"
	      Loc.fprint loc0 fprint_dcon2 d2c1 fprint_dcon2 d2c2;
	    Err.abort ();
	  end

      | SE2proj (s2e1, sl1), SE2proj (s2e2, sl2) ->
	  if slab2_syneq sl1 sl2 then sexp2_equal_solve loc0 s2e1 s2e2
	  else begin
	    PR.eprintf "%a: sexp2_equal_solve: %a <> %a\n"
	      Loc.fprint loc0 fprint_sexp2 s2e10 fprint_sexp2 s2e20;
	    Err.abort ();
	  end

      | SE2sel (s2e1, i), _ when sexp2_is_Var s2e1 ->
	  sexp2_equal_solve_sel_Var loc0 s2e1 i s2e20

      | _, SE2sel (s2e2, i) when sexp2_is_Var s2e2 ->
	  sexp2_equal_solve_sel_Var loc0 s2e2 i s2e10

      | SE2tyarr (s2e1_elt, s2ess1_dim), SE2tyarr (s2e2_elt, s2ess2_dim) ->
	  begin
	    sexp2_equal_solve loc0 s2e1_elt s2e2_elt;
	    sexp2_list_list_equal_solve loc0 s2ess1_dim s2ess2_dim
	  end

      | SE2tyrec (k1, (npf1, ls2es1)), SE2tyrec (k2, (npf2, ls2es2)) ->
	  if tyrec_kind_eq k1 k2 then
	    if npf1 == npf2 then
	      labsexp2_list_equal_solve loc0 ls2es1 ls2es2
	    else EM3.pfarity_errmsg loc0
	  else EM3.tyrec_kind_errmsg loc0 k1 k2

      | SE2union (s2i1, ls2es1), SE2union (s2i2, ls2es2) ->
	  begin
	    sexp2_equal_solve loc0 s2i1 s2i2;
	    labsexp2_list_equal_solve loc0 ls2es1 ls2es2
	  end

      | _, _ when sexp2_is_abscon s2e10 && sexp2_is_abscon s2e20 ->
	  sexp2_equal_solve_abscon loc0 s2e10 s2e20

      | _, _ when sexp2_head_var_test s2e10 s2e20 ->
	  sexp2_equal_solve_appvar loc0 s2e10 s2e20

      | _, _ -> begin
	  let s2t = s2e10.sexp2_sort in
	    if srt2_is_impredicative s2t then begin
	      sexp2_tyleq_solve loc0 s2e10 s2e20;
	      sexp2_tyleq_solve loc0 s2e20 s2e10
	    end else begin
	      SEnv3.prop_eqeq_add loc0 s2e10 s2e20
	    end
	end
(* end of [sexp2_equal_solve] *)

and sexp2_list_equal_solve loc0
  (s2es1: sexp2 list) (s2es2: sexp2 list): unit =
(*
  let () =
    PR.fprintf stdout "sexp2_list_equal_solve: s2es1 = %a\n"
      fprint_sexp2_list s2es1 in
  let () =
    PR.fprintf stdout "sexp2_list_equal_solve: s2es2 = %a\n"
      fprint_sexp2_list s2es2 in
*)
  match compare (List.length s2es1) (List.length s2es2) with
    | 0 -> List.iter2 (sexp2_equal_solve loc0) s2es1 s2es2
    | i -> begin
	PR.eprintf
	  "%a: sexp2_list_equal_solve error: unequal length: (%a) <> (%a)\n"
	  Loc.fprint loc0 fprint_sexp2_list s2es1 fprint_sexp2_list s2es2;
	Err.abort ();
      end
(* end of [sexp2_list_equal_solve] *)

and sexp2_list_list_equal_solve loc0
  (s2ess1: sexp2 list list) (s2ess2: sexp2 list list): unit =
(*
  let () =
    PR.fprintf stdout "sexp2_list_list_equal_solve: s2ess1 = %a\n"
      fprint_sexp2_list_list s2ess1 in
  let () =
    PR.fprintf stdout "sexp2_list_list_equal_solve: s2ess2 = %a\n"
      fprint_sexp2_list_list s2ess2 in
*)
  match compare (List.length s2ess1) (List.length s2ess2) with
    | 0 -> List.iter2 (sexp2_list_equal_solve loc0) s2ess1 s2ess2
    | i -> begin
	PR.eprintf
	  "%a: sexp2_list_list_equal_solve error: unequal length\n"
	  Loc.fprint loc0;
	Err.abort ();
      end
(* end of [sexp2_list_list_equal_solve] *)

and labsexp2_list_equal_solve loc0
  (ls2es1: labsexp2 list) (ls2es2: labsexp2 list): unit =
(*
  let () =
    PR.fprintf stdout "labsexp2_list_equal_solve: ls2es1 = %a\n"
      fprint_labsexp2_list ls2es1 in
  let () =
    PR.fprintf stdout "labsexp2_list_equal_solve: ls2es2 = %a\n"
      fprint_labsexp2_list ls2es2 in
*)
  let rec aux ls2es1 ls2es2 = match ls2es1, ls2es2 with
    | [], [] -> ()
    | (l1, s2e1) :: ls2es1, (l2, s2e2) :: ls2es2 ->
	if Lab.eq l1 l2 then
	  (sexp2_equal_solve loc0 s2e1 s2e2; aux ls2es1 ls2es2)
	else begin
	  PR.eprintf
	    "%a: labsexp2_list_equal_solve: label mismatch: %a <> %a\n"
	    Loc.fprint loc0 Lab.fprint l1 Lab.fprint l2;
	  Err.abort ();
	end
      | _, _ -> error_of_deadcode "ats_trans3: labsexp2_list_equal_solve: aux" in
    match compare (List.length ls2es1) (List.length ls2es2) with
      | 0 -> aux ls2es1 ls2es2
      | i -> begin
	  PR.eprintf
	    "%a: labsexp2_list_equal_solve error: unequal length\n"
	    Loc.fprint loc0;
	  Err.abort ();
	end
(* end of [labsexp2_list_equal_solve] *)

and sexp2_equal_solve_abscon loc0 (s2e1: sexp2) (s2e2: sexp2): unit =
  let rec aux_solve s2e1 s2e2 =
    match s2e1.sexp2_node, s2e2.sexp2_node with
      | SE2app (s2e11, s2es12), SE2app (s2e21, s2es22) ->
	  begin
	    aux_solve s2e11 s2e21;
	    sexp2_list_equal_solve loc0 s2es12 s2es22
	  end
      | _, _ -> () in
  let rec aux_check s2e1 s2e2 =
    match s2e1.sexp2_node, s2e2.sexp2_node with
      | SE2cst s2c1, SE2cst s2c2 -> scst2_eq s2c1 s2c2
      | SE2app (s2e1, _), SE2app (s2e2, _) -> aux_check s2e1 s2e2
      | _, _ -> false in
    if aux_check s2e1 s2e2 then aux_solve s2e1 s2e2
    else SEnv3.prop_add loc0 (sexp2_bool false)
(* end of [sexp2_equal_solve_abscon] *)

and sexp2_equal_solve_appvar loc0
  (s2e1: sexp2) (s2e2: sexp2): unit =
  let rec aux s2e1 s2e2 =
    match s2e1.sexp2_node, s2e2.sexp2_node with
      | SE2app (s2e11, s2es12), SE2app (s2e21, s2es22) ->
	  begin
	    aux s2e11 s2e21;
	    sexp2_list_equal_solve loc0 s2es12 s2es22
	  end
      | _, _ -> () in
    aux s2e1 s2e2
(* end of [sexp2_equal_solve_appvar] *)

(* ****** ****** *)

and sexp2_eff_leq_solve loc0
  (sf2e1: seff2) (sf2e2: seff2): unit =
(*
  let () =
      PR.fprintf stdout "%a: sexp2_eff_leq_solve: %a = %a?\n"
	Loc.fprint loc0 fprint_seff2 sf2e1 fprint_seff2 sf2e2 in
*)
  let ans = match sf2e2 with
    | SEFF2set (effs, [s2e2])
	when Eff.effset_is_nil effs -> begin
	  let s2e2 = sexp2_whnf s2e2 in match s2e2.sexp2_node with
	    | SE2Var s2V2 ->
		let s2e1 = sexp2_eff sf2e1 in
		let () = sexp2_equal_solve_Var loc0 s2V2 s2e2 s2e1 in
		  true
	    | _ -> begin
		let sf2e1 = SEFF2set (effs, [s2e2]) in
		  seff2_contain_seff2 sf2e2 sf2e1
	      end
	end
    | _ -> seff2_contain_seff2 sf2e2 sf2e1 in
    if not (ans) then begin
      PR.eprintf "%a: sexp2_eff_leq_solve: %a <!= %a\n"
	Loc.fprint loc0 fprint_seff2 sf2e1 fprint_seff2 sf2e2;
      Err.abort ();
    end
(* end of [sexp2_eff_leq_solve] *)

(* ****** ****** *)

and sexp2_szleq_solve loc0 (s2e1: sexp2) (s2e2: sexp2): unit =
  let sz2e1 = sexp2_sizeof s2e1 and sz2e2 = sexp2_sizeof s2e2 in
    if not (szexp2_leq sz2e1 sz2e2) then
      begin
	PR.eprintf "%a: sexp2_szleq_solve: %a != %a\n"
	  Loc.fprint loc0 fprint_szexp2 sz2e1 fprint_szexp2 sz2e2;
	Err.abort ();
      end
(* end of [sexp2_szleq_solve] *)

and sexp2_szeqeq_solve loc0 (s2e1: sexp2) (s2e2: sexp2): unit =
  let sz2e1 = sexp2_sizeof s2e1 and sz2e2 = sexp2_sizeof s2e2 in
    if not (szexp2_syneq sz2e1 sz2e2) then
      begin
	PR.eprintf "%a: sexp2_szeqeq_solve: %a != %a\n"
	  Loc.fprint loc0 fprint_szexp2 sz2e1 fprint_szexp2 sz2e2;
	Err.abort ();
      end
(* end of [sexp2_szeqeq_solve] *)

(*

and sexp2_szeq_solve_at loc0 (s2e1: sexp2) (s2e2: sexp2): unit =
  let s2e1 = sexp2_whnf s2e1 and s2e2 = sexp2_whnf s2e2 in
    match
      un_sexp2_at_viewtype_addr_view s2e1,
      un_sexp2_at_viewtype_addr_view s2e2
    with
      | Some (s2e1, s2l1), Some (s2e2, s2l2) -> begin
	  sexp2_szeq_solve loc0 s2e1 s2e2;
	  sexp2_equal_solve loc0 s2l1 s2l2
	end
      | _, _ -> begin
	  PR.eprintf "%a: sexp2_szeq_solve_at: %a != %a\n"
	    Loc.fprint loc0 fprint_sexp2 s2e1 fprint_sexp2 s2e2;
	  Err.abort ();
	end

*)

(* ****** ****** *)

and sexp2_void_solve loc0 (s2e: sexp2): unit =
  match s2e.sexp2_node with
    | SE2out _ -> ()
    | _ when Void_t0ype.eq_exp s2e -> ()
    | _ -> begin
	PR.eprintf "%a: sexp2_void_solve: not void: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end
(* end of [sexp2_void_solve] *)

(* ****** ****** *)

and sexp2_tyleq_solve loc0 (s2e10: sexp2) (s2e20: sexp2): unit =
  let s2e10 = sexp2_whnf s2e10 and s2e20 = sexp2_whnf s2e20 in
(*
  let () = PR.fprintf stdout "sexp2_tyleq_solve:\n" in
  let () = PR.fprintf stdout "  s2e1 = %a\n" fprint_sexp2 s2e10 in
  let () = PR.fprintf stdout "  s2e2 = %a\n" fprint_sexp2 s2e20 in
*)
    match s2e10.sexp2_node, s2e20.sexp2_node with
      | _, SE2top _ -> begin
	  if sexp2_is_nonlin s2e10 then begin
	    sexp2_szeqeq_solve loc0 s2e10 s2e20
	  end else begin
	    PR.eprintf "%a: sexp2_tyleq_solve: %a <!= %a\n"
	      Loc.fprint loc0 fprint_sexp2 s2e10 fprint_sexp2 s2e20;
	    Err.abort ()
	  end
	end
      | _, SE2union (s2i2, _) when sexp2_is_intinf_zero s2i2 ->
	  sexp2_szeqeq_solve loc0 s2e10 s2e20

      | SE2app (s2e1, s2es1), SE2cst s2c2 -> begin
	  match s2e1.sexp2_node with
	    | SE2cst s2c1 when scst2_leq s2c1 s2c2 -> ()
	    | _ -> begin
		PR.eprintf "%a: sexp2_tyleq_solve: %a <!= %a\n"
		  Loc.fprint loc0 fprint_sexp2 s2e10 fprint_sexp2 s2e20;
		Err.abort ();
	      end
	end

      | SE2app (s2e1, s2es1), SE2app (s2e2, s2es2) -> begin
	  match s2e1.sexp2_node, s2e2.sexp2_node with
	    | SE2cst s2c1, SE2cst s2c2 when scst2_leq s2c1 s2c2 -> begin
		match s2c1.scst2_arg with
		  | None -> sexp2_list_equal_solve loc0 s2es1 s2es2
		  | Some vars -> sexp2_list_tyleq_solve_with_vars loc0 s2es1 s2es2 vars
	      end
	    | _, _ -> begin (* sound but incomplete! *)
		sexp2_equal_solve loc0 s2e1 s2e2;
		sexp2_list_equal_solve loc0 s2es1 s2es2
	      end
	end

      | SE2clo (knd1, s2e1), SE2clo (knd2, s2e2) -> begin
	  clokind_equal_solve loc0 knd1 knd2; sexp2_tyleq_solve loc0 s2e1 s2e2;
	end

      | SE2cst s2c1, SE2cst s2c2 ->
	  if scst2_neq s2c1 s2c2 then begin
	    PR.eprintf "%a: sexp2_tyleq_solve: %a <!= %a\n"
	      Loc.fprint loc0 fprint_scst2 s2c1 fprint_scst2 s2c2;
	    Err.abort ();
	  end 

      | SE2datcon (d2c1, s2ls1), SE2datcon (d2c2, s2ls2) ->
	  if dcon2_eq d2c1 d2c2 then
	    sexp2_list_equal_solve loc0 s2ls1 s2ls2
	  else begin
	    PR.eprintf "%a: sexp2_tyleq_solve: %a <> %a\n"
	      Loc.fprint loc0 fprint_dcon2 d2c1 fprint_dcon2 d2c2;
	    Err.abort ();
	  end

      | SE2fun (lin1, sf2e1, (npf1, s2es1), s2e1),
	SE2fun (lin2, sf2e2, (npf2, s2es2), s2e2) -> begin
	  funlinear_equal_solve loc0 lin1 lin2;
	  pfarity_equal_solve loc0 npf1 npf2;
	  sexp2_eff_leq_solve loc0 sf2e1 sf2e2;
	  sexp2_list_tyleq_solve loc0 s2es2 s2es1;
	  sexp2_tyleq_solve loc0 s2e1 s2e2;
	end (* end of [SE2fun] *)

      | SE2refarg (refval1, s2e11, s2e12),
	SE2refarg (refval2, s2e21, s2e22) -> begin
	  refargptr_equal_solve loc0 refval1 refval2;
	  sexp2_tyleq_solve loc0 s2e11 s2e21;
	  sexp2_tyleq_solve loc0 s2e22 s2e12;
	end

      | SE2tyarr (s2e1_elt, s2ess1_dim), SE2tyarr (s2e2_elt, s2ess2_dim) ->
	  begin
	    sexp2_tyleq_solve loc0 s2e1_elt s2e2_elt;
	    sexp2_list_list_equal_solve loc0 s2ess1_dim s2ess2_dim;
	  end

      | SE2tylst s2es1, SE2tylst s2es2 ->
	  sexp2_list_tyleq_solve loc0 s2es1 s2es2

      | SE2tyrec (k1, (npf1, ls2es1)), SE2tyrec (k2, (npf2, ls2es2)) ->
	  if tyrec_kind_eq k1 k2 then
	    if npf1 == npf2 then labsexp2_list_tyleq_solve loc0 ls2es1 ls2es2
	    else EM3.pfarity_errmsg loc0
	  else EM3.tyrec_kind_errmsg loc0 k1 k2

      | SE2tyrec (k1, (npf1, ls2es1)), SE2vararg s2e2 -> begin
	  match k1 with
	    | TYRECflt _ -> begin
		if npf1 == 0 then
		  let s2e1 =
		    sexp2_tylst (List.map (function (l, s2e) -> s2e) ls2es1) in
		    sexp2_tyleq_solve loc0 s2e1 s2e2
		else EM3.pfarity_errmsg loc0
	      end
	    | _ -> EM3.flatness_errmsg loc0 k1
	end

      | SE2union (s2i1, ls2es1), SE2union (s2i2, ls2es2) ->
	  begin
	    sexp2_equal_solve loc0 s2i1 s2i2;
	    labsexp2_list_tyleq_solve loc0 ls2es1 ls2es2
	  end

      | SE2var s2v1, SE2var s2v2 ->
	  if svar2_neq s2v1 s2v2 then begin
	    PR.eprintf "%a: sexp2_tyleq_solve: %a <> %a\n"
	      Loc.fprint loc0 fprint_svar2 s2v1 fprint_svar2 s2v2;
	    Err.abort ();
	  end

      | SE2Var s2V1, SE2Var s2V2 when sVar2_eq s2V1 s2V2 -> ()
(*
      | SE2Var s2V1, _ when s2V1.sVar2_equal ->
	  sexp2_equal_solve_Var loc0 s2V1 s2e10 s2e20
      | _, SE2Var s2V2 when s2V2.sVar2_equal ->
	  sexp2_equal_solve_Var loc0 s2V2 s2e20 s2e10
*)
      | SE2Var s2V1, _ -> sexp2_tyleq_solve_Var_l loc0 s2V1 s2e20
      | _, SE2Var s2V2 -> sexp2_tyleq_solve_Var_r loc0 s2e10 s2V2 s2e20

      | _, SE2uni (s2vs2, s2ps2, s2e2) ->
	  let () = SEnv3.env_push () in
	  let s2e2 =
	    let sub = SEnv3.sexp2_hypo_inst_and_add loc0 s2vs2 s2ps2 in
	      sexp2_subst sub s2e2 in
	  let () = sexp2_tyleq_solve loc0 s2e10 s2e2 in
	  let () = SEnv3.env_pop_and_add () in ()
			       
      | SE2uni (s2vs1, s2ps1, s2e1), _ ->
	  let () = SEnv3.env_push () in
	  let (s2vs2, s2ps2, s2e2) = sexp2_abstract s2e20 in
	  let () = SEnv3.svar_list_add s2vs2 in
	  let () = SEnv3.hypo_prop_list_add s2ps2 in
	  let s2e1 =
	    let sub = SEnv3.sexp2_inst_and_add loc0 s2vs1 s2ps1 in
	      sexp2_subst sub s2e1 in
	  let () = sexp2_tyleq_solve loc0 s2e1 s2e2 in
	  let () = SEnv3.env_pop_and_add () in ()

      | SE2exi (s2vs1, s2ps1, s2e1), _ ->
	  let () = SEnv3.env_push () in
	  let s2e1 =
	    let sub = SEnv3.sexp2_hypo_inst_and_add loc0 s2vs1 s2ps1 in
	      sexp2_subst sub s2e1 in
	  let () = sexp2_tyleq_solve loc0 s2e1 s2e20 in
	  let () = SEnv3.env_pop_and_add () in ()
			       
      | _, SE2exi (s2vs2, s2ps2, s2e2) ->
	  let () = SEnv3.env_push () in
	  let (s2vs1, s2ps1, s2e1) = sexp2_open s2e10 in
	  let () = SEnv3.svar_list_add s2vs1 in
	  let () = SEnv3.hypo_prop_list_add s2ps1 in
	  let s2e2 =
	    let sub = SEnv3.sexp2_inst_and_add loc0 s2vs2 s2ps2 in
	      sexp2_subst sub s2e2 in
	  let () = sexp2_tyleq_solve loc0 s2e1 s2e2 in
	  let () = SEnv3.env_pop_and_add () in ()

      | SE2VarApp (s2V11, s2e12), SE2VarApp (s2V21, s2e22) ->
	  if sVar2_eq s2V11 s2V21 then sexp2_equal_solve loc0 s2e12 s2e22
	  else if Stamps.subset s2V11.sVar2_svs s2V21.sVar2_svs then
	    begin
	      s2V21.sVar2_link <- Some (sexp2_Var s2V11);
	      srt2_solve s2V21.sVar2_arg_sort s2e12.sexp2_sort;
	      sexp2_equal_solve loc0 s2e12 s2e22;
	    end
	  else if Stamps.subset s2V21.sVar2_svs s2V11.sVar2_svs then
	    begin
	      s2V11.sVar2_link <- Some (sexp2_Var s2V21);
	      srt2_solve s2V11.sVar2_arg_sort s2e22.sexp2_sort;
	      sexp2_equal_solve loc0 s2e12 s2e22;
	    end
	  else begin
	    PR.eprintf "%a: sexp2_tyleq_solve: %a <!= %a\n"
	      Loc.fprint loc0 fprint_sexp2 s2e10 fprint_sexp2 s2e20;
	    Err.abort ();
	  end

      | SE2VarApp (s2V11, s2e12), _ ->
	  sexp2_tyleq_solve_VarApp loc0 true (*left*) s2V11 s2e12 s2e20
      | _, SE2VarApp (s2V21, s2e22) ->
	  sexp2_tyleq_solve_VarApp loc0 false (*right*) s2V21 s2e22 s2e10 

      | _, _ -> begin
	  if not (sexp2_syneq s2e10 s2e20) then begin
	    PR.eprintf "%a: sexp2_tyleq_solve: %a <!= %a\n"
	      Loc.fprint loc0 fprint_sexp2 s2e10 fprint_sexp2 s2e20;
	    Err.abort ();
	  end
	end
(* end of [sexp2_tyleq_solve] *)

(* ****** ****** *)

and sexp2_list_tyleq_solve loc0
  (s2es1: sexp2 list) (s2es2: sexp2 list): unit =
  let aux s2e1 s2e2 = sexp2_tyleq_solve loc0 s2e1 s2e2 in
    match compare (List.length s2es1) (List.length s2es2) with
      | 0 -> List.iter2 aux s2es1 s2es2
      | _ -> begin
	  PR.eprintf
	    "%a: sexp2_list_tyleq_solve: type lists of unequal length: %a <> %a\n"
	    Loc.fprint loc0 fprint_sexp2_list s2es1 fprint_sexp2_list s2es2;
	  Err.abort ();
	end
(* end of [sexp2_list_tyleq_solve] *)

and labsexp2_list_tyleq_solve loc0
  (ls2es1: labsexp2 list) (ls2es2: labsexp2 list): unit =
  match ls2es1, ls2es2 with
    | (l1, s2e1) :: ls2es1, (l2, s2e2) :: ls2es2 ->
	if Lab.eq l1 l2 then begin
	  sexp2_tyleq_solve loc0 s2e1 s2e2;
	  labsexp2_list_tyleq_solve loc0 ls2es1 ls2es2
	end else begin
	  PR.eprintf
	    "%a: labsexp2_list_tyleq_solve: label mismatch: %a <> %a\n"
	    Loc.fprint loc0 Lab.fprint l1 Lab.fprint l2;
	  Err.abort ();
	end
    | [], [] -> ()
    | _, _ -> begin
	PR.eprintf
	  "%a: labsexp2_list_tyleq_solve: type lists of unequal length\n"
	  Loc.fprint loc0;
	Err.abort ();
      end
(* end of [labsexp2_list_tyleq_solve] *)

(* ****** ****** *)

and labsexp2_list_tyrec_tyleq_solve loc0
  (k1: tyrec_kind) (npf1: int) (ls2es1: labsexp2 list) (s2e2: sexp2): unit =
  let ls2es1 = SEnv3.labsexp2_list_open_and_add ls2es1 in
  let rec aux s2e2 = match s2e2.sexp2_node with
    | SE2exi (s2vs2, s2ps2, s2e2) ->
	let s2e2 =
	  let sub = SEnv3.sexp2_inst_and_add loc0 s2vs2 s2ps2 in
	    sexp2_subst sub s2e2 in
	  aux (sexp2_whnf s2e2)
    | SE2tyrec (k2, (npf2, ls2es2)) ->
	if tyrec_kind_eq k1 k2 then
	  if npf1 == npf2 then
	    labsexp2_list_tyleq_solve loc0 ls2es1 ls2es2
	  else EM3.pfarity_errmsg loc0
	else EM3.tyrec_kind_errmsg loc0 k1 k2
    | SE2Var s2V2 ->
	let s2e1 = sexp2_tyrec k1 npf1 ls2es1 in
	  sexp2_tyleq_solve_Var_r loc0 s2e1 s2V2 s2e2
    | _ -> begin
	PR.eprintf
	  "%a: labsexp2_list_tyrec_tyleq_solve: not a record type: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e2;
	Err.abort ();
      end in
    aux s2e2
(* end of [labsexp2_list_tyrec_tyleq_solve] *)

(* ****** ****** *)

and sexp2_list_tyleq_solve_with_vars loc0
  (s2es1: sexp2 list) (s2es2: sexp2 list)
  (vars: (Syn.sid option * srt2 * int) list): unit =
  match vars with
    | [] -> ()
    | (_, _, i) :: vars -> begin match s2es1, s2es2 with
	| s2e1 :: s2es1, s2e2 :: s2es2 ->
	    let () =
	      if i > 0 then sexp2_tyleq_solve loc0 s2e1 s2e2
	      else if i < 0 then sexp2_tyleq_solve loc0 s2e2 s2e1
	      else sexp2_equal_solve loc0 s2e1 s2e2 in
	      sexp2_list_tyleq_solve_with_vars loc0 s2es1 s2es2 vars
	| _, _ -> error_of_deadcode "ats_trans3: sexp2_tyleq_solve_with_vars"
      end
(* end of [sexp2_list_tyleq_solve_with_vars] *)

(* ****** ****** *)

and sexp2_tyleq_solve_Var_l loc0 s2V (ub: sexp2): unit =
  if not (sexp2_occurs s2V ub) then
    let () = s2V.sVar2_ubs <-  ub :: s2V.sVar2_ubs in
      List.iter
	(function lb -> sexp2_tyleq_solve loc0 lb ub) (s2V.sVar2_lbs)
  else begin
    PR.eprintf "%a: sexp2_tyleq_solve_Var_l: <%a> occurs in <%a>.\n"
      Loc.fprint loc0 fprint_sVar2 s2V fprint_sexp2 ub;
    Err.abort ();
  end
(* end of [sexp2_tyleq_solve_Var_l] *)

and sexp2_tyleq_solve_Var_r loc0
  (lb: sexp2) (s2V: sVar2) (s2e: sexp2): unit =
  if not (sexp2_occurs s2V lb) then
    let s2t1 = s2V.sVar2_sort and s2t2 = lb.sexp2_sort in
    let () =
      if not (srt2_leq s2t2 s2t1) then begin
	PR.eprintf "%a: sexp2_tyleq_solve_Var_r: %a: %a <!= %a\n"
	  Loc.fprint loc0 fprint_sVar2 s2V fprint_srt2 s2t2 fprint_srt2 s2t1;
	Err.abort ();
      end in
    let () = s2V.sVar2_sort <- s2t2 in
    let () = s2e.sexp2_sort <- s2t2 in
    let () =  s2V.sVar2_lbs <-  lb :: s2V.sVar2_lbs in
      List.iter (function ub -> sexp2_tyleq_solve loc0 lb ub) (s2V.sVar2_ubs)
  else begin
    PR.eprintf "%a: sexp2_tyleq_solve_Var_r: <%a> occurs in <%a>.\n"
      Loc.fprint loc0 fprint_sVar2 s2V fprint_sexp2 lb;
    Err.abort ();
  end
(* end of [sexp2_tyleq_solve_Var_r] *)

(* ****** ****** *)

and sexp2_tyleq_solve_VarApp loc0
  (is_left: bool) (s2V: sVar2) (arg: sexp2) (bound: sexp2): unit =
  let s2t_res = bound.sexp2_sort in match bound.sexp2_node with
    | (SE2cst _ | SE2var _) ->
	let () = srt2_solve s2V.sVar2_arg_sort srt2_unit in
	let s2t_fun = srt2_fun [srt2_unit] s2t_res in
	let () = sexp2_equal_solve loc0 arg sexp2_unit in
	let s2v = svar2_new srt2_unit in
	let s2e_lam = sexp2_lam_with_sort s2t_fun [s2v] bound in
	  if not (sexp2_occurs s2V bound) then
	    SEnv3.sVar2_assign_with_error loc0 s2V s2e_lam
	  else EM3.occur_check_errmsg loc0 s2V s2e_lam
    | SE2app (s2e, s2es) -> begin match s2e.sexp2_node with
	| SE2cst s2c ->
	    let (s2v, s2c_args) = SEnv3.scst2_closure loc0 s2V.sVar2_svs s2c in
	    let s2e_body = sexp2_app_with_sort s2t_res s2e s2c_args in
	    let s2t_arg = s2v.svar2_sort in
	    let () = srt2_solve s2V.sVar2_arg_sort s2t_arg in
	    let s2t_fun = srt2_fun [s2t_arg] s2t_res in
	    let s2e_lam = sexp2_lam_with_sort s2t_fun [s2v] s2e_body in
	    let () = 
	      if not (sexp2_occurs s2V s2e_lam) then
		SEnv3.sVar2_assign_with_error loc0 s2V s2e_lam
	      else EM3.occur_check_errmsg loc0 s2V s2e_lam in
	    let s2e_app = sexp2_subst [(s2v, arg)] s2e_body in
	      if is_left then sexp2_tyleq_solve loc0 s2e_app bound
	      else sexp2_tyleq_solve loc0 bound s2e_app
	| _ -> begin
	    PR.eprintf "%a: sexp2_tyleq_solve_VarApp: SE2app: <%a> = <%a>.\n"
	      Loc.fprint loc0 fprint_sVar2 s2V fprint_sexp2 s2e;
	    Err.abort ();
	  end
      end (* end of [SE2app] *)
    | SE2fun (lin, sf2e, (npf, s2es_arg), s2e_res) ->
	let () = srt2_solve s2V.sVar2_arg_sort srt2_unit in
	let stamps = s2V.sVar2_svs in
	let (s2es_arg_new, s2e_res_new) =
	  let f s2e =
	    SEnv3.sexp2_VarApp_new_with_stamps loc0 stamps s2e.sexp2_sort in
	    (List.map f s2es_arg, f s2e_res) in
	let bound_new =
	  sexp2_fun_with_sort s2t_res lin sf2e (npf, s2es_arg_new) s2e_res_new in
	let s2t_fun = srt2_fun [srt2_unit] s2t_res in
	let () =
	  let () = sexp2_equal_solve loc0 arg sexp2_unit in
	  let s2v = svar2_new srt2_unit in
	  let s2e_lam = sexp2_lam_with_sort s2t_fun [s2v] bound_new in
	    if not (sexp2_occurs s2V s2e_lam) then
	      SEnv3.sVar2_assign_with_error loc0 s2V s2e_lam
	    else EM3.occur_check_errmsg loc0 s2V s2e_lam in
	  if is_left then sexp2_tyleq_solve loc0 bound_new bound
	  else sexp2_tyleq_solve loc0 bound bound_new
    | SE2tyrec (is_flat, (npf, ls2es)) ->
	let () = srt2_solve s2V.sVar2_arg_sort srt2_unit in
	let stamps = s2V.sVar2_svs in
	let ls2es_new =
	  List.map
	    (function (l, s2e) ->
	       (l, SEnv3.sexp2_VarApp_new_with_stamps loc0 stamps s2e.sexp2_sort))
	    ls2es in
	let bound_new = sexp2_tyrec_with_sort s2t_res is_flat npf ls2es_new in
	let s2t_fun = srt2_fun [srt2_unit] s2t_res in
	let () =
	  let () = sexp2_equal_solve loc0 arg sexp2_unit in
	  let s2v = svar2_new srt2_unit in
	  let s2e_lam = sexp2_lam_with_sort s2t_fun [s2v] bound_new in
	    if not (sexp2_occurs s2V s2e_lam) then
	      SEnv3.sVar2_assign_with_error loc0 s2V s2e_lam
	    else EM3.occur_check_errmsg loc0 s2V s2e_lam in
	  if is_left then sexp2_tyleq_solve loc0 bound_new bound
	  else sexp2_tyleq_solve loc0 bound bound_new
    | _ -> begin
	PR.eprintf "%a: sexp2_tyleq_solve_VarApp: <%a> = <%a>.\n"
	  Loc.fprint loc0 fprint_sVar2 s2V fprint_sexp2 bound;
	Err.abort ();
      end
(* end of [sexp2_tyleq_solve_VarApp] *)

(* ****** ****** *)

and sexp2_equal_solve_Var loc0
  (s2V1: sVar2) (s2e1: sexp2) (s2e2: sexp2): unit =
(*
  let () = 
    PR.fprintf stdout "sexp2_equal_solve_Var: <%a> <- <%a>.\n"
      fprint_sVar2 s2V1 fprint_sexp2 s2e2 in
  let () = 
    PR.fprintf stdout "sexp2_equal_solve_Var: %a.sVar2_svs = (%a)\n"
      fprint_sVar2 s2V1 fprint_stamps s2V1.sVar2_svs in
  let () = 
    PR.fprintf stdout "sexp2_equal_solve_Var: fvs(%a) = (%a)\n"
      fprint_sexp2 s2e2 fprint_stamps (sexp2_fvs_0 s2e2) in
*)
  if not (sexp2_occurs s2V1 s2e2) then
    if Stamps.subset (sexp2_fvs_0 s2e2) s2V1.sVar2_svs then
      let s2t1 = s2V1.sVar2_sort and s2t2 = s2e2.sexp2_sort in
      let () =
	if not (srt2_leq s2t2 s2t1) then begin
	  PR.eprintf "%a: sexp2_equal_solve_Var: %a <- %a: %a <!= %a\n"
	    Loc.fprint loc0 fprint_sVar2 s2V1 fprint_sexp2 s2e2
	    fprint_srt2 s2t2 fprint_srt2 s2t1;
	  Err.abort ();
	end in
      let () = s2V1.sVar2_sort <- s2t2 in
      let () = s2e1.sexp2_sort <- s2t2 in
      let () = s2V1.sVar2_link <- Some s2e2 in begin
	  List.iter
	    (function lb -> sexp2_tyleq_solve loc0 lb s2e2) (s2V1.sVar2_lbs);
	  List.iter
	    (function ub -> sexp2_tyleq_solve loc0 s2e2 ub) (s2V1.sVar2_ubs);
	end
    else begin
      PR.fprintf stdout "%a: sexp2_equal_solve_Var: <%a> <!- <%a>.\n" 
	Loc.fprint loc0 fprint_sVar2 s2V1 fprint_sexp2 s2e2;
      SEnv3.prop_eqeq_add loc0 s2e1 s2e2
    end
  else begin
    PR.eprintf "%a: sexp2_equal_solve_Var: <%a> occurs in <%a>.\n"
      Loc.fprint loc0 fprint_sVar2 s2V1 fprint_sexp2 s2e2;
    Err.abort ();
  end 
(* end of [sexp2_equal_solve_Var] *)

and sexp2_equal_solve_sel_Var loc0
  (s2e1: sexp2) (i: int) (s2e2: sexp2) =
  let s2V1 = match s2e1.sexp2_node with
    | SE2Var s2V -> s2V
    | _ -> error_of_deadcode
	"ats_staexp2_solve: sexp2_equal_solve_sel_Var" in
  let s2ts1 =
    let s2t = s2e1.sexp2_sort in match srt2_link_rmv s2t with
      | SRT2tup s2ts -> s2ts
      | _ -> error "sexp2_equal_solve_sel_Var" in
  let s2es1 =
    let loc = s2V1.sVar2_loc in
    let stamps = s2V1.sVar2_svs in
      List.map
	(function s2t -> SEnv3.sexp2_Var_new_with_stamps loc s2t stamps)
	s2ts1 in
  let () = s2V1.sVar2_link <- Some (sexp2_tup s2es1) in
    sexp2_equal_solve loc0 (List.nth s2es1 i) s2e2
(* end of [sexp2_equal_solve_sel_Var] *)

(* ****** ****** *)

let rec sexp2_hyeq_solve loc0 s2e1 s2e2: unit =
  let s2e1 = sexp2_whnf s2e1 and s2e2 = sexp2_whnf s2e2 in
(*
  let () = PR.fprintf stdout "sexp2_hyeq_solve:\n" in
  let () = PR.fprintf stdout "  s2e1 = %a\n" fprint_sexp2 s2e1 in
  let () = PR.fprintf stdout "  s2e2 = %a\n" fprint_sexp2 s2e2 in
*)
    match s2e1.sexp2_node, s2e2.sexp2_node with
      | _, _ when sexp2_is_abscon s2e1 && sexp2_is_abscon s2e2 ->
	  sexp2_hyeq_solve_con loc0 s2e1 s2e2
      | SE2cst s2c1, SE2cst s2c2 when scst2_eq s2c1 s2c2 -> ()
      | SE2var s2v1, SE2var s2v2 when svar2_eq s2v1 s2v2 -> ()
      | SE2var s2v1, _ ->
	  let s2t_var = s2v1.svar2_sort in
	  let s2t_exp = s2e2.sexp2_sort in
	  let () =
	    if not (srt2_leq s2t_var s2t_exp) then s2v1.svar2_sort <- s2t_exp in
	    (SB.svar_add s2v1 s2e2; SEnv3.hypo_bind_add s2v1 s2e2)
      | _, SE2var s2v2 ->
	  let s2t_var = s2v2.svar2_sort in
	  let s2t_exp = s2e1.sexp2_sort in
	  let () =
	    if not (srt2_leq s2t_var s2t_exp) then s2v2.svar2_sort <- s2t_exp in
	    (SB.svar_add s2v2 s2e1; SEnv3.hypo_bind_add s2v2 s2e1)
      | SE2clo (knd1, s2e1), SE2clo (knd2, s2e2) -> begin
	  sexp2_hyeq_solve loc0 s2e1 s2e2
	end
      | SE2fun (lin1, sf2e1, (npf1, s2es11), s2e12),
	SE2fun (lin2, sf2e2, (npf2, s2es21), s2e22) -> begin
	  sexp2_list_hyeq_solve loc0 s2es21 s2es11;
	  sexp2_hyeq_solve loc0 s2e12 s2e22;
	end
      | _, _ -> SEnv3.hypo_eqeq_add s2e1 s2e2
(* end of [sexp2_hyeq_solve] *)

and sexp2_list_hyeq_solve loc0
  (s2es1: sexp2 list) (s2es2: sexp2 list): unit =
  match compare (List.length s2es1) (List.length s2es2) with
    | 0 -> List.iter2 (sexp2_hyeq_solve loc0) s2es1 s2es2
    | i -> SEnv3.hypo_prop_add (sexp2_bool false)
(* end of [sexp2_list_hyeq_solve] *)

and sexp2_hyeq_solve_con loc0 (s2e1: sexp2) (s2e2: sexp2): unit =
(*
  let () = PR.fprintf stdout "sexp2_hyeq_solve_con:\n" in
  let () = PR.fprintf stdout "  s2e1 = %a\n" fprint_sexp2 s2e1 in
  let () = PR.fprintf stdout "  s2e2 = %a\n" fprint_sexp2 s2e2 in
*)
  let rec aux_solve s2e1 s2e2 =
    match s2e1.sexp2_node, s2e2.sexp2_node with
      | SE2app (s2e11, s2es12), SE2app (s2e21, s2es22) ->
	  begin
	    aux_solve s2e11 s2e21;
	    sexp2_list_hyeq_solve loc0 s2es12 s2es22
	  end
      | _, _ -> () in
  let rec aux_check s2e1 s2e2 =
    match s2e1.sexp2_node, s2e2.sexp2_node with
      | SE2cst s2c1, SE2cst s2c2 -> scst2_eq s2c1 s2c2
      | SE2app (s2e1, _), SE2app (s2e2, _) -> aux_check s2e1 s2e2
      | _, _ -> false in
    if aux_check s2e1 s2e2 then aux_solve s2e1 s2e2
    else SEnv3.hypo_prop_add (sexp2_bool false)
(* end of [sexp2_hyeq_solve_con] *)

(* ****** ****** *)

(* end of [ats_staexp2_solve.ml] *)
