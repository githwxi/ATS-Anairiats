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

(* mainly for handling constraints *)

open Ats_misc
open Ats_staexp2
open Ats_staexp2_util
open Ats_stacst2

open Ats_patcst2
open Ats_staenv3

module A = Array
module BI = Big_int
module PR = Printf

module Err = Ats_error
module Loc = Ats_location
module FM = Ats_solver_fm
module SB = Ats_svar_bind

(* some type abbreviations *)

type loc = Loc.location

(* a standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_constraint: "; Err.error s;
end (* end of [error] *)

(* ****** ****** *)

type saexp3 = (* static address expression *)
  | SAE3cst of scst2 (* abstract constant *)
  | SAE3exp of sexp2
  | SAE3var of svar2
  | SAE3null 
  | SAE3padd of saexp3 * siexp3


and sbexp3 = (* static boolean expression *)
  | SBE3cst of scst2 (* abstract constant *)
  | SBE3exp of sexp2
  | SBE3var of svar2
  | SBE3bool of bool
  | SBE3badd of sbexp3 * sbexp3
  | SBE3bmul of sbexp3 * sbexp3
  | SBE3bneg of sbexp3
  | SBE3ieq of siexp3 * siexp3
  | SBE3igte of siexp3 * siexp3
  | SBE3ilt of siexp3 * siexp3
  | SBE3ineq of siexp3 * siexp3
  | SBE3pgte of saexp3 * saexp3
  | SBE3plt of saexp3 * saexp3
  | SBE3peq of saexp3 * saexp3
  | SBE3pneq of saexp3 * saexp3

and siexp3 = (* static integer expression *)
  | SIE3cst of scst2 (* abstract constant *)
  | SIE3int of intinf
  | SIE3exp of sexp2
  | SIE3var of svar2
  | SIE3iadd of siexp3 * siexp3
  | SIE3imul of siexp3 * siexp3
  | SIE3pdiff of saexp3 * saexp3

(* ****** ****** *)

let rec fprint_saexp3 (out: out_channel) (s3ae: saexp3): unit =
  match s3ae with
    | SAE3cst s2c -> fprint_scst2 out s2c
    | SAE3exp s2e -> fprint_sexp2 out s2e
    | SAE3var s2v -> fprint_svar2 out s2v
    | SAE3padd (s3ae, s3ie) -> begin
	PR.fprintf out "SAE3padd(%a, %a)" fprint_saexp3 s3ae fprint_siexp3 s3ie
      end (* end of [SAE3padd] *)
    | SAE3null -> PR.fprintf out "null"
(* end of [fprint_saexp3] *)

and fprint_sbexp3 (out: out_channel) (s3be: sbexp3): unit =
  match s3be with
    | SBE3cst s2c -> fprint_scst2 out s2c
    | SBE3exp s2e -> fprint_sexp2 out s2e
    | SBE3var s2v -> fprint_svar2 out s2v
    | SBE3bool b -> if b then PR.fprintf out "true" else PR.fprintf out "false"

    | SBE3bmul (s3be1, s3be2) ->
	PR.fprintf out "SBE3bmul(%a, %a)" fprint_sbexp3 s3be1 fprint_sbexp3 s3be2
    | SBE3badd (s3be1, s3be2) ->
	PR.fprintf out "SBE3badd(%a, %a)" fprint_sbexp3 s3be1 fprint_sbexp3 s3be2
    | SBE3bneg s3be -> PR.fprintf out "SBE3bneg(%a)" fprint_sbexp3 s3be

    | SBE3ieq (s3ie1, s3ie2) ->
	PR.fprintf out "SBE3ieq(%a, %a)" fprint_siexp3 s3ie1 fprint_siexp3 s3ie2
    | SBE3igte (s3ie1, s3ie2) ->
	PR.fprintf out "SBE3igte(%a, %a)" fprint_siexp3 s3ie1 fprint_siexp3 s3ie2
    | SBE3ilt (s3ie1, s3ie2) ->
	PR.fprintf out "SBE3ilt(%a, %a)" fprint_siexp3 s3ie1 fprint_siexp3 s3ie2
    | SBE3ineq (s3ie1, s3ie2) ->
	PR.fprintf out "SBE3igte(%a, %a)" fprint_siexp3 s3ie1 fprint_siexp3 s3ie2

    | SBE3peq (s3ae1, s3ae2) ->
	PR.fprintf out "SBE3peq(%a, %a)" fprint_saexp3 s3ae1 fprint_saexp3 s3ae2
    | SBE3pgte (s3ae1, s3ae2) ->
	PR.fprintf out "SBE3pgte(%a, %a)" fprint_saexp3 s3ae1 fprint_saexp3 s3ae2
    | SBE3plt (s3ae1, s3ae2) ->
	PR.fprintf out "SBE3plt(%a, %a)" fprint_saexp3 s3ae1 fprint_saexp3 s3ae2
    | SBE3pneq (s3ae1, s3ae2) ->
	PR.fprintf out "SBE3pneq(%a, %a)" fprint_saexp3 s3ae1 fprint_saexp3 s3ae2
(* end of [fprint_sbexp3] *)

and fprint_siexp3 (out: out_channel) (s3ie: siexp3): unit =
  match s3ie with
    | SIE3cst s2c -> fprint_scst2 out s2c
    | SIE3exp s2e -> fprint_sexp2 out s2e
    | SIE3var s2v -> fprint_svar2 out s2v
    | SIE3int i -> fprint_intinf out i
    | SIE3iadd (s3ie1, s3ie2) ->
	PR.fprintf out "SIE3iadd(%a, %a)" fprint_siexp3 s3ie1 fprint_siexp3 s3ie2
    | SIE3imul (s3ie1, s3ie2) ->
	PR.fprintf out "SIE3imul(%a, %a)" fprint_siexp3 s3ie1 fprint_siexp3 s3ie2
    | SIE3pdiff (s3ae1, s3ae2) ->
	PR.fprintf out "SIE3pdiff(%a, %a)" fprint_saexp3 s3ae1 fprint_saexp3 s3ae2
(* end of [fprint_siexp3] *)

let fprint_sbexp3_list
  (out: out_channel) (s3bes: sbexp3 list): unit =
  fprint_list_with_sep fprint_sbexp3 out s3bes ";"

(* ****** ****** *)

let the_scst2set: ScstSet.t ref = ref (ScstSet.empty)

let scst2set_get (): ScstSet.t = !the_scst2set

let scst2set_init (): unit = the_scst2set := ScstSet.empty

let scst2set_add (s2c: scst2): unit =
  the_scst2set := ScstSet.add s2c !the_scst2set

(* ****** ****** *)

type fundef = {
  fundef_cst: scst2;
  fundef_arg: sexp2 list;
  fundef_res: svar2;
  fundef_rel : sbexp3 option;
} (* end of [fundef] *)

let the_fundef_list: fundef list ref = ref []
let the_fundef_list_list: fundef list list ref = ref []

let fundefs_init (): unit = begin
  the_fundef_list := []; the_fundef_list_list := []
end (* end of [fundefs_init] *)

let fundefs_get (): fundef list = !the_fundef_list

let fundefs_pop (): unit =
  match !the_fundef_list_list with
  | fds :: fdss -> begin
      the_fundef_list := fds; the_fundef_list_list := fdss
    end
  | [] -> error "ats_constraint: fundefs_pop"
(* end of [fundefs_pop] *)

let fundefs_push (): unit = begin
  the_fundef_list_list := !the_fundef_list :: !the_fundef_list_list;
end (* end of [fundefs_push] *)

let fundefs_find (s2c: scst2) (s2es: sexp2 list): svar2 option =
  let rec aux fds = match fds with
    | [] -> None
    | fd :: fds ->
	if scst2_eq s2c fd.fundef_cst then
	  if sexp2_list_syneq s2es fd.fundef_arg then Some fd.fundef_res
	  else aux fds
	else aux fds in
    aux !the_fundef_list
(* end of [fundefs_find] *)

(* ****** ****** *)

(* some functions for forming static boolean and integer expressions *)

let sbexp3_true: sbexp3 = SBE3bool true
let sbexp3_false: sbexp3 = SBE3bool false

let sbexp3_bneg (s3be: sbexp3): sbexp3 =
  match s3be with 
    | SBE3bool b -> SBE3bool (not b)
    | SBE3badd (s3be1, s3be2) -> SBE3bmul (SBE3bneg s3be1, SBE3bneg s3be2)
    | SBE3bmul (s3be1, s3be2) -> SBE3badd (SBE3bneg s3be1, SBE3bneg s3be2)
    | SBE3bneg s3be -> s3be
    | SBE3igte (s3ie1, s3ie2) -> SBE3ilt (s3ie1, s3ie2)
    | SBE3ilt (s3ie1, s3ie2) -> SBE3igte (s3ie1, s3ie2)
    | SBE3ieq (s3ie1, s3ie2) -> SBE3ineq (s3ie1, s3ie2)
    | SBE3ineq (s3ie1, s3ie2) -> SBE3ieq (s3ie1, s3ie2)
    | SBE3pgte (s3ae1, s3ae2) -> SBE3plt (s3ae1, s3ae2)
    | SBE3plt (s3ae1, s3ae2) -> SBE3pgte (s3ae1, s3ae2)
    | SBE3peq (s3ae1, s3ae2) -> SBE3pneq (s3ae1, s3ae2)
    | SBE3pneq (s3ae1, s3ae2) -> SBE3peq (s3ae1, s3ae2)
    | _ -> SBE3bneg s3be
(* end of [sbexp3_bneg] *)

let sbexp3_beq (s3be1: sbexp3) (s3be2: sbexp3): sbexp3 =
  match s3be1, s3be2 with
    | SBE3bool b1, _ -> if b1 then s3be2 else sbexp3_bneg s3be2
    | _, SBE3bool b2 -> if b2 then s3be1 else sbexp3_bneg s3be1
    | _, _ -> begin
	SBE3badd (SBE3bmul (s3be1, s3be2), SBE3bmul (SBE3bneg s3be1, SBE3bneg s3be2))
      end
(* end of [sbexp3_beq] *)

let sbexp3_bneq (s3be1: sbexp3) (s3be2: sbexp3): sbexp3 =
  match s3be1, s3be2 with
    | SBE3bool b1, _ -> if b1 then sbexp3_bneg s3be2 else s3be2
    | _, SBE3bool b2 -> if b2 then sbexp3_bneg s3be1 else s3be1
    | _, _ -> begin
	SBE3badd (SBE3bmul (s3be1, SBE3bneg s3be2), SBE3bmul (SBE3bneg s3be1, s3be2))
      end
(* end of [sbexp3_bneq] *)

let sbexp3_badd (s3be1: sbexp3) (s3be2: sbexp3): sbexp3 =
  match s3be1, s3be2 with
    | SBE3bool b1, _ -> if b1 then sbexp3_true else s3be2
    | _, SBE3bool b2 -> if b2 then sbexp3_true else s3be1
    | _, _ -> SBE3badd (s3be1, s3be2)
(* end of [sbexp3_badd] *)

let sbexp3_bmul (s3be1: sbexp3) (s3be2: sbexp3): sbexp3 =
  match s3be1, s3be2 with
    | SBE3bool b1, _ -> if b1 then s3be2 else sbexp3_false
    | _, SBE3bool b2 -> if b2 then s3be1 else sbexp3_false
    | _, _ -> SBE3bmul (s3be1, s3be2)
(* end of [sbexp3_bmul] *)

let sbexp3_igte  (s3ie1: siexp3) (s3ie2: siexp3): sbexp3 =
  match s3ie1, s3ie2 with
    | SIE3int i1, SIE3int i2 -> SBE3bool (BI.ge_big_int i1 i2)
    | _, _ -> SBE3igte (s3ie1, s3ie2)
(* end of [sbexp3_igte] *)

let sbexp3_ilt  (s3ie1: siexp3) (s3ie2: siexp3): sbexp3 =
  match s3ie1, s3ie2 with
    | SIE3int i1, SIE3int i2 -> SBE3bool (BI.lt_big_int i1 i2)
    | _, _ -> SBE3ilt (s3ie1, s3ie2)
(* end of [sbexp3_ilt] *)

let sbexp3_ieq  (s3ie1: siexp3) (s3ie2: siexp3): sbexp3 =
  match s3ie1, s3ie2 with
    | SIE3int i1, SIE3int i2 -> SBE3bool (BI.eq_big_int i1 i2)
    | _, _ -> SBE3ieq (s3ie1, s3ie2)
(* end of [sbexp3_ieq] *)

let sbexp3_ineq  (s3ie1: siexp3) (s3ie2: siexp3): sbexp3 =
  match s3ie1, s3ie2 with
    | SIE3int i1, SIE3int i2 -> SBE3bool (not (BI.eq_big_int i1 i2))
    | _, _ -> SBE3ineq (s3ie1, s3ie2)
(* end of [sbexp3_ineq] *)

let sbexp3_pgt  (s3ae1: saexp3) (s3ae2: saexp3): sbexp3 =
  SBE3plt (s3ae2, s3ae1)

let sbexp3_pgte (s3ae1: saexp3) (s3ae2: saexp3): sbexp3 =
  SBE3pgte (s3ae1, s3ae2)

let sbexp3_plt  (s3ae1: saexp3) (s3ae2: saexp3): sbexp3 =
  SBE3plt (s3ae1, s3ae2)

let sbexp3_plte (s3ae1: saexp3) (s3ae2: saexp3): sbexp3 =
  SBE3pgte (s3ae2, s3ae1)

let sbexp3_peq  (s3ae1: saexp3) (s3ae2: saexp3): sbexp3 =
  match s3ae1, s3ae2 with
    | SAE3var s2v1, SAE3var s2v2 when svar2_eq s2v1 s2v2 -> sbexp3_true
    | _, _ -> SBE3peq (s3ae1, s3ae2)
(* end of [sbexp3_peq] *)

let sbexp3_pneq (s3ae1: saexp3) (s3ae2: saexp3): sbexp3 =
  match s3ae1, s3ae2 with
    | SAE3var s2v1, SAE3var s2v2 when svar2_eq s2v1 s2v2 -> sbexp3_false
    | _, _ -> SBE3pneq (s3ae1, s3ae2)
(* end of [sbexp3_pneq] *)

(* ****** ****** *)

let siexp3_iadd (s3ie1: siexp3) (s3ie2: siexp3): siexp3 =
  match s3ie1, s3ie2 with
    | SIE3int i, _ when intinf_is_zero i -> s3ie2
    | _, SIE3int i when intinf_is_zero i -> s3ie1
    | SIE3int i1, SIE3int i2 -> SIE3int (BI.add_big_int i1 i2)
    | _, _ -> SIE3iadd (s3ie1, s3ie2)
(* end of [siexp3_iadd] *)

let siexp3_imul (s3ie1: siexp3) (s3ie2: siexp3): siexp3 =
  match s3ie1, s3ie2 with
    | SIE3int i, _ when intinf_is_zero i -> SIE3int i
    | _, SIE3int i when intinf_is_zero i -> SIE3int i
    | SIE3int i, _ when intinf_is_unit i -> s3ie2
    | _, SIE3int i when intinf_is_unit i -> s3ie1
    | SIE3int i1, SIE3int i2 -> SIE3int (BI.mult_big_int i1 i2)
    | _, _ -> SIE3imul (s3ie1, s3ie2)
(* end of [siexp3_imul] *)


let siexp3_one = SIE3int (intinf_unit)
let siexp3_neg_one = SIE3int (intinf_neg_unit)

let siexp3_succ (s3ie: siexp3): siexp3 = siexp3_iadd s3ie siexp3_one
let siexp3_pred (s3ie: siexp3): siexp3 = siexp3_iadd s3ie siexp3_neg_one

let siexp3_ineg (s3ie: siexp3): siexp3 = siexp3_imul siexp3_neg_one s3ie
let siexp3_isub (s3ie1: siexp3) (s3ie2: siexp3): siexp3 =
  siexp3_iadd s3ie1 (siexp3_ineg s3ie2)

let siexp3_pdiff (s3ae1: saexp3) (s3ae2: saexp3): siexp3 =
  SIE3pdiff (s3ae1, s3ae2)

let rec saexp3_padd (s3ae1: saexp3) (s3ie2: siexp3): saexp3 =
  match s3ae1 with
    | SAE3padd (s3ae11, s3ie12) ->
	saexp3_padd s3ae11 (siexp3_iadd s3ie12 s3ie2)
    | _ -> begin match s3ie2 with
	| SIE3int i when intinf_is_zero i -> s3ae1
	| _ -> SAE3padd (s3ae1, s3ie2)
      end
(* end of [saexp3_add] *)

let saexp3_psucc (s3ae: saexp3): saexp3 = saexp3_padd s3ae siexp3_one
let saexp3_ppred (s3ae: saexp3): saexp3 = saexp3_padd s3ae siexp3_neg_one

(* some translation functions *)

let rec sbexp3_of_sexp2 (s2e: sexp2): sbexp3 option =
(*
  let () = PR.printf "sbexp3_of_sexp2: s2e = %a\n" fprint_sexp2 s2e in
*)
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2app (s2e1, s2es2) -> begin
	match s2e1.sexp2_node with
	  | SE2cst s2c -> sbexp3_of_scst2_sexp2_list s2c s2es2
	  | _ -> None
      end
    | SE2cst s2c -> begin
	if True_bool.eq_cst s2c then Some (SBE3bool true)
	else if False_bool.eq_cst s2c then Some (SBE3bool false)
	else (scst2set_add s2c; Some (SBE3cst s2c))
      end
    | SE2var s2v -> Some (SBE3var s2v)
    | SE2eqeq (s2e1, s2e2) -> sbexp3_of_eqeq s2e1 s2e2
    | SE2mlt (metric, metric_bound) ->
	sbexp3_of_sexp2 (sexp2_mlt_reduce metric metric_bound)
    | _ -> None
(* end of [sbexp3_of_sexp2] *)

and sbexp3_of_eqeq (s2e1: sexp2) (s2e2: sexp2): sbexp3 option =
  let s2t = s2e1.sexp2_sort in
    if srt2_is_int s2t then
      match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	| Some s3ie1, Some s3ie2 -> Some (sbexp3_ieq s3ie1 s3ie2)
	| _, _ -> None
    else if srt2_is_addr s2t then
      match saexp3_of_sexp2 s2e1, saexp3_of_sexp2 s2e2 with
	| Some s3ae1, Some s3ae2 -> Some (sbexp3_peq s3ae1 s3ae2)
	| _, _ -> None
    else if srt2_is_bool s2t then
      match sbexp3_of_sexp2 s2e1, sbexp3_of_sexp2 s2e2 with
	| Some s3be1, Some s3be2 -> Some (sbexp3_beq s3be1 s3be2)
	| _, _ -> None
    else if (sexp2_syneq s2e1 s2e2) then Some (sbexp3_true)
    else None
(* end of [sbexp3_of_eqeq] *)

and sbexp3_of_bind (s2v: svar2) (s2e: sexp2): sbexp3 option =
(*
  let () =
    PR.fprintf stdout "sbexp3_of_bind: s2v = %a\n" fprint_svar2 s2v in
  let () =
    PR.fprintf stdout "sbexp3_of_bind: s2e = %a\n" fprint_sexp2 s2e in
*)
  let os3be = sbexp3_of_eqeq (sexp2_var s2v) s2e in
    (SB.svar_add s2v s2e; os3be)
(* end of [sbexp3_of_bind] *)

and sbexp3_of_scst2_sexp2_list (s2c: scst2) (s2es: sexp2 list): sbexp3 option =
  if Badd.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match sbexp3_of_sexp2 s2e1, sbexp3_of_sexp2 s2e2 with
	  | Some s3be1, Some s3be2 -> Some (sbexp3_badd s3be1 s3be2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Bmul.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match sbexp3_of_sexp2 s2e1, sbexp3_of_sexp2 s2e2 with
	  | Some s3be1, Some s3be2 -> Some (sbexp3_bmul s3be1 s3be2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Beq.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match sbexp3_of_sexp2 s2e1, sbexp3_of_sexp2 s2e2 with
	  | Some s3be1, Some s3be2 -> Some (sbexp3_beq s3be1 s3be2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Bneg.eq_cst s2c then match s2es with
    | [s2e] -> begin
	match sbexp3_of_sexp2 s2e with
	  | Some s3be -> Some (sbexp3_bneg s3be)
	  | None -> None
      end
    | _ -> None
  else if Igt.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (sbexp3_ilt s3ie2 s3ie1)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Igte.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (sbexp3_igte s3ie1 s3ie2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Ilt.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (sbexp3_ilt s3ie1 s3ie2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Ilte.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (sbexp3_igte s3ie2 s3ie1)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Ieq.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (sbexp3_ieq s3ie1 s3ie2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Ineq.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (sbexp3_ineq s3ie1 s3ie2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Pgt.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, saexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ae2 -> Some (sbexp3_pgt s3ae1 s3ae2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Pgte.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, saexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ae2 -> Some (sbexp3_pgte s3ae1 s3ae2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Plt.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, saexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ae2 -> Some (sbexp3_plt s3ae1 s3ae2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Plte.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, saexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ae2 -> Some (sbexp3_plte s3ae1 s3ae2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Peq.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, saexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ae2 -> Some (sbexp3_peq s3ae1 s3ae2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else if Pneq.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, saexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ae2 -> Some (sbexp3_pneq s3ae1 s3ae2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: sbexp3_of_scst2_sexp2_list"
  else None
(* end of [sbexp3_of_scst2_sexp2_list] *)

(* ****** ****** *)

and siexp3_of_sexp2 (s2e: sexp2): siexp3 option =
(*
  let () = PR.printf "siexp3_of_sexp2: s2e = %a\n" fprint_sexp2 s2e in
*)
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2app (s2e1, s2es2) -> begin
	match s2e1.sexp2_node with
	  | SE2cst s2c -> siexp3_of_scst2_sexp2_list s2c s2es2
	  | _ -> None
      end
    | SE2cst s2c -> (scst2set_add s2c; Some (SIE3cst s2c))
    | SE2int i -> Some (SIE3int i)
    | SE2var s2v -> Some (SIE3var s2v)
    | _ -> None
(* end of [siexp3_of_sexp2] *)

and siexp3_of_scst2_sexp2_list (s2c: scst2) (s2es: sexp2 list): siexp3 option =
  if Ineg.eq_cst s2c then match s2es with
    | [s2e] -> begin
	match siexp3_of_sexp2 s2e with
	  | Some s3ie -> Some (siexp3_ineg s3ie)
	  | _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: siexp3_of_scst2_sexp2_list: ineg"

  else if Iadd.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (siexp3_iadd s3ie1 s3ie2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: siexp3_of_scst2_sexp2_list"

  else if Isub.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (siexp3_isub s3ie1 s3ie2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: siexp3_of_scst2_sexp2_list"

  else if Imul.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match siexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ie1, Some s3ie2 -> Some (siexp3_imul s3ie1 s3ie2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: siexp3_of_scst2_sexp2_list: imul"

  else if Idiv.eq_cst s2c then
    let s2c_r = Idiv_r.make_cst () in
    let s2v = fundefs_replace srt2_int s2c_r s2es in
      Some (SIE3var s2v)

  else if Pdiff.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, saexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ae2 -> Some (siexp3_pdiff s3ae1 s3ae2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: siexp3_of_scst2_sexp2_list: pdiff"

  else if Iabs.eq_cst s2c then
    let s2c_r = Iabs_r.make_cst () in
    let s2v = fundefs_replace srt2_int s2c_r s2es in
      Some (SIE3var s2v)

  else if Nsub.eq_cst s2c then
    let s2c_r = Nsub_r.make_cst () in
    let s2v = fundefs_replace srt2_int s2c_r s2es in
      Some (SIE3var s2v)

  else if Imax.eq_cst s2c then 
    let s2c_r = Imax_r.make_cst () in
    let s2v = fundefs_replace srt2_int s2c_r s2es in
      Some (SIE3var s2v)

  else if Imin.eq_cst s2c then 
    let s2c_r = Imin_r.make_cst () in
    let s2v = fundefs_replace srt2_int s2c_r s2es in
      Some (SIE3var s2v)

  else if VTsizeof.eq_cst s2c then
(*
    let () =
      PR.fprintf stdout "siexp3: VTsizeof: s2es = %a\n" fprint_sexp2_list s2es in
*)
    let s2e = match s2es with
      | [s2e] -> s2e
      |	_ -> error_of_deadcode "siexp3_of_scst2_sexp2_list: VTsizeof" in
    let s2e_size = sexp2_top_with_sort srt2_int s2e in
    let s2c_r = VTsizeof_r.make_cst () in
    let s2v = fundefs_replace srt2_int s2c_r [s2e_size] in
(*
    let () =
      PR.fprintf stdout "siexp3: VTsizeof: s2v = %a\n" fprint_svar2 s2v in
*)
      Some (SIE3var s2v)

  else None
(* end of [siexp3_of_scst2_sexp2_list] *)

(* ****** ****** *)

and saexp3_of_sexp2 (s2e: sexp2): saexp3 option =
(*
  let () = PR.printf "saexp3_of_sexp2: s2e = %a\n" fprint_sexp2 s2e in
*)
  let s2e = sexp2_whnf s2e in match s2e.sexp2_node with
    | SE2app (s2e1, s2es2) -> begin match s2e1.sexp2_node with
	| SE2cst s2c -> saexp3_of_scst2_sexp2_list s2c s2es2
	| _ -> None
      end
    | SE2cst s2c ->
        if Null_addr.eq_cst s2c then Some (SAE3null)
	else (scst2set_add s2c; Some (SAE3cst s2c))
    | SE2var s2v -> Some (SAE3var s2v)
    | _ -> None
(* end of [saexp3_of_sexp2] *)

and saexp3_of_scst2_sexp2_list (s2c: scst2) (s2es: sexp2 list): saexp3 option =
  if Padd.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ie2 -> Some (saexp3_padd s3ae1 s3ie2)
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: saexp3_of_scst2_sexp2_list"
  else if Psub.eq_cst s2c then match s2es with
    | [s2e1; s2e2] -> begin
	match saexp3_of_sexp2 s2e1, siexp3_of_sexp2 s2e2 with
	  | Some s3ae1, Some s3ie2 ->
	      Some (saexp3_padd s3ae1 (siexp3_ineg s3ie2))
	  | _, _ -> None
      end
    | _ -> error_of_deadcode "ats_constraint: saexp3_of_scst2_sexp2_list"
  else None
(* end of [saexp3_of_scst2_sexp2_list] *)

and fundefs_add (s2c: scst2) (s2es: sexp2 list) (s2v: svar2): unit =
(*
  let () =
    PR.fprintf stdout "fundefs_add: s2c = %a\n" fprint_scst2 s2c in
  let () =
    PR.fprintf stdout "fundefs_add: s2es = %a\n" fprint_sexp2_list s2es in
  let () =
    PR.fprintf stdout "fundefs_add: s2v = %a\n" fprint_svar2 s2v in
*)
  let s2e_rel =
    sexp2_app_with_sort srt2_bool
      (sexp2_cst s2c) (s2es @ [sexp2_var s2v]) in
  let os3be = sbexp3_of_sexp2 s2e_rel in
  let fd = {
    fundef_cst= s2c;
    fundef_arg= s2es;
    fundef_res= s2v;
    fundef_rel= os3be;
  } in (the_fundef_list := fd :: !the_fundef_list)
(* end of [fundefs_add] *)

and fundefs_replace (s2t: srt2) (s2c: scst2) (s2es: sexp2 list): svar2 =
  match fundefs_find s2c s2es with
    | None -> let s2v = svar2_new s2t in (fundefs_add s2c s2es s2v; s2v)
    | Some s2v -> s2v
(* end of [fundefs_replace] *)

(* ****** ****** *)

let sbexp3_of_hypo3 (h3p: hypo3): sbexp3 option =
  match h3p.hypo3_node with
    | HYPO3prop s2p -> sbexp3_of_sexp2 s2p
    | HYPO3eqeq (s2e1, s2e2) -> sbexp3_of_eqeq s2e1 s2e2
    | HYPO3bind (s2v, s2e) -> sbexp3_of_bind s2v s2e
(* end of [sbexp3_of_hypo3] *)

(* solving integer constraints with the FM approach *)

type intvec = FM.intvec
type svar2indmap = int SvarMap.t
type scst2indmap = int ScstMap.t

let svar2ind_find (m: svar2indmap) (s2v: svar2): int option =
  try Some (SvarMap.find s2v m) with Not_found -> None

let scst2ind_find (m: scst2indmap) (s2c: scst2): int option =
  try Some (ScstMap.find s2c m) with Not_found -> None

let rec siexp3_intvec loc0
  (sz: int) (cm: scst2indmap) (vm: svar2indmap) (s3ie: siexp3): intvec =
(*
  let () =
    PR.fprintf stdout "siexp3_intvec: s3ie = %a\n" fprint_siexp3 s3ie in
*)
  let vec = A.make sz intinf_zero in
  let () = siexp3_intvec_aux loc0 intinf_unit vec cm vm s3ie in vec
(* end of [siex[3_intvec] *)

and siexp3_intvec_aux loc0 (c: intinf)
  (vec: intvec) (cm: scst2indmap) (vm: svar2indmap) (s3ie: siexp3): unit =
  let rec aux (c: intinf) (s3ie: siexp3): unit = match s3ie with
    | SIE3cst s2c -> begin
	match scst2ind_find cm s2c with
	  | Some n -> (vec.(n) <- BI.add_big_int vec.(n) c)
	  | None -> begin
	      PR.fprintf stderr "%a: siexp3_intvec_aux: SIE3cst: %a\n"
		Loc.fprint loc0 fprint_scst2 s2c;
	      Err.abort ();
	    end
      end
    | SIE3var s2v -> begin
	match svar2ind_find vm s2v with
	  | Some n -> (vec.(n) <- BI.add_big_int vec.(n) c)
	  | None -> begin
	      PR.fprintf stderr "%a: siexp3_intvec_aux: SIE3var: %a\n"
		Loc.fprint loc0 fprint_svar2 s2v;
	      Err.abort ();
	    end 
      end 
    | SIE3iadd (s3ie1, s3ie2) -> (aux c s3ie1; aux c s3ie2)
    | SIE3int i -> (vec.(0) <- BI.add_big_int vec.(0) (BI.mult_big_int c i))
    | SIE3imul (s3ie1, s3ie2) -> begin
	match s3ie1, s3ie2 with
	  | SIE3int i, _ -> aux (BI.mult_big_int c i) s3ie2
	  | _, SIE3int i -> aux (BI.mult_big_int c i) s3ie1
	  | _, _ -> begin
	      PR.fprintf stderr
		"%a: siexp3_intvec_aux: SIE3mul: nonlinear term: %a\n"
		Loc.fprint loc0 fprint_siexp3 s3ie;
	      Err.abort ();
	    end
      end
    | SIE3pdiff (s3ae1, s3ae2) -> begin
        saexp3_intvec_aux loc0 c vec cm vm s3ae1;
	saexp3_intvec_aux loc0 (BI.minus_big_int c) vec cm vm s3ae2
      end
    | SIE3exp s2e -> begin
	PR.fprintf stderr "%a: siexp3_intvec_aux: SIE3exp: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end in
    aux c s3ie
(* end of [siexp3_intvec_aux] *)

and saexp3_intvec loc0
  (sz: int) (cm: scst2indmap) (vm: svar2indmap) (s3ae: saexp3): intvec =
  let vec = A.make sz intinf_zero in
  let () = saexp3_intvec_aux loc0 intinf_unit vec cm vm s3ae in vec
(* end of [saexp3_intvec] *)

and saexp3_intvec_aux loc0 (c: intinf)
  (vec: intvec) (cm: scst2indmap) (vm: svar2indmap) (s3ae: saexp3): unit =
  let rec aux (s3ae: saexp3): unit = match s3ae with
    | SAE3var s2v -> begin
	match svar2ind_find vm s2v with
	  | Some n -> (vec.(n) <- BI.add_big_int vec.(n) c)
	  | None -> begin
	      PR.fprintf stderr "%a: saexp3_intvec_aux: SAE3var: %a\n"
		Loc.fprint loc0 fprint_svar2 s2v;
	      Err.abort ();
	    end 
      end 
    | SAE3cst s2c -> begin
	match scst2ind_find cm s2c with
	  | Some n -> (vec.(n) <- BI.add_big_int vec.(n) c)
	  | None -> begin
	      PR.fprintf stderr "%a: saexp3_intvec_aux: SAE3cst: %a\n"
		Loc.fprint loc0 fprint_scst2 s2c;
	      Err.abort ();
	    end
      end
    | SAE3padd (s3ae1, s3ie2) ->
	(aux s3ae1; siexp3_intvec_aux loc0 c vec cm vm s3ie2)
    | SAE3null -> ()
    | SAE3exp s2e -> begin
	PR.fprintf stderr "%a: saexp3_intvec_aux: SAE3exp: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end in
    aux s3ae
(* end of [saexp3_intvec_aux] *)

let sbexp3_icstr loc0 (sz: int)
  (cm: scst2indmap) (vm: svar2indmap) (s3be: sbexp3): FM.icstr =
(*
  let () =
    PR.fprintf stdout "sbexp3_icstr: s3be = %a\n" fprint_sbexp3 s3be in
*)
  let rec aux (s3be: sbexp3): FM.icstr = match s3be with
    | SBE3bool b -> if b then FM.ICconj [] else FM.ICdisj []
    | SBE3cst s2c -> begin
	match scst2ind_find cm s2c with
	  | Some n ->
	      let vec = A.make sz intinf_zero in
	      let () = vec.(n) <- intinf_unit
	      and () = vec.(0) <- intinf_neg_unit in
		FM.ICgte vec
          | None -> begin
	      PR.fprintf stderr "%a: sbexp3_icstr: aux: SBE3cst: %a\n"
		Loc.fprint loc0 fprint_scst2 s2c;
	      Err.abort ();
	    end
      end
    | SBE3var s2v -> begin
	match svar2ind_find vm s2v with
	  | Some n ->
	      let vec = A.make sz intinf_zero in
	      let () = vec.(n) <- intinf_unit
	      and () = vec.(0) <- intinf_neg_unit in
		FM.ICgte vec
	  | None -> begin
	      PR.fprintf stderr "%a: sbexp3_icstr: aux: SBE3var: %a\n"
		Loc.fprint loc0 fprint_svar2 s2v;
	      Err.abort ();
	    end
      end 

    | SBE3bneg s3be -> FM.icstr_negate (aux s3be)
    | SBE3badd (s3be1, s3be2) -> FM.ICdisj [aux s3be1; aux s3be2]
    | SBE3bmul (s3be1, s3be2) -> FM.ICconj [aux s3be1; aux s3be2]

    | SBE3igte (s3ie1, s3ie2) ->
	let vec =
	  siexp3_intvec loc0 sz cm vm (siexp3_isub s3ie1 s3ie2) in
	  FM.ICgte vec
    | SBE3ilt (s3ie1, s3ie2) ->
	let vec =
	  siexp3_intvec loc0 sz cm vm (siexp3_isub s3ie1 s3ie2) in
	  FM.IClt vec

    | SBE3ieq (s3ie1, s3ie2) ->
	let vec =
	  siexp3_intvec loc0 sz cm vm (siexp3_isub s3ie1 s3ie2) in
	  FM.ICeq vec
    | SBE3ineq (s3ie1, s3ie2) ->
	let vec =
	  siexp3_intvec loc0 sz cm vm (siexp3_isub s3ie1 s3ie2) in
	  FM.ICneq vec

    | SBE3pgte (s3ae1, s3ae2) ->
	let vec =
	  siexp3_intvec loc0 sz cm vm (siexp3_pdiff s3ae1 s3ae2) in
	  FM.ICgte vec
    | SBE3plt (s3ae1, s3ae2) ->
	let vec =
	  siexp3_intvec loc0 sz cm vm (siexp3_pdiff s3ae1 s3ae2) in
	  FM.IClt vec

    | SBE3peq (s3ae1, s3ae2) ->
	let vec =
	  siexp3_intvec loc0 sz cm vm (siexp3_pdiff s3ae1 s3ae2) in
	  FM.ICeq vec
    | SBE3pneq (s3ae1, s3ae2) ->
	let vec =
	  siexp3_intvec loc0 sz cm vm (siexp3_pdiff s3ae1 s3ae2) in
	  FM.ICneq vec

    | SBE3exp s2e -> begin
	PR.fprintf stderr "%a: sbexp3_icstr3: aux: SBE3exp: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2e;
	Err.abort ();
      end in
    aux s3be
(* end of [sbexp3_icstr] *)

exception UnsolvedConstraint of sbexp3 list * sexp2

let solve_fm loc0 (s2vs: svar2 list) (s3bes: sbexp3 list) (s2p: sexp2): unit =
(*
  let () =
    PR.fprintf stdout "solve_fm: s2vs = %a\n" fprint_svar2_list s2vs in
  let () =
    PR.fprintf stdout "solve_fm: s3bes = %a\n" fprint_sbexp3_list s3bes in
  let () =
    PR.fprintf stdout "solve_fm: s2p = %a\n" fprint_sexp2 s2p in
*)
  let os3be = sbexp3_of_sexp2 s2p in
  let s2cs = scst2set_get () and fds = fundefs_get () in
  let s3bes =
    let rec aux s3bes = function
      | [] -> s3bes
      | fd :: fds ->
	  let s3bes = match fd.fundef_rel with
	    | None -> s3bes
	    | Some s3be -> s3be :: s3bes in
	    aux s3bes fds in
      aux s3bes fds in
  let s3be = match os3be with
    | Some s3be -> s3be
    | None -> begin
	PR.fprintf stderr "%a: solve_fm: %a\n"
	  Loc.fprint loc0 fprint_sexp2 s2p;
	Err.abort ();
      end in
  let (n, cm) =
    let aux s2c (i, cm) = (i+1, ScstMap.add s2c i cm) in
      ScstSet.fold aux s2cs (1, ScstMap.empty) in
  let (n, vm) =
    let aux (i, vm) s2v = (i+1, SvarMap.add s2v i vm) in
      List.fold_left aux (n, SvarMap.empty) s2vs in
  let (n, vm) =
    let aux (i, vm) fd = (i+1, SvarMap.add fd.fundef_res i vm) in
      List.fold_left aux (n, vm) fds in
  let ics_asmp = List.map (sbexp3_icstr loc0 n cm vm) s3bes in
  let ic_conc = sbexp3_icstr loc0 n cm vm s3be in
(*
  let () =
    PR.fprintf stdout "solve_fm: ic_asmp:\n%a\n" FM.fprint_icstr_list ics_asmp in
  let () =
    PR.fprintf stdout "solve_fm: ic_conc = %a\n" FM.fprint_icstr ic_conc in
*)
    begin
      try FM.solve_icstrlist [] [] (FM.icstr_negate ic_conc :: ics_asmp)
      with
	| FM.Contradiction -> ()
	| FM.UnsolvedConstraint _ -> raise (UnsolvedConstraint (s3bes, s2p))
    end
(* end of [solve_fm] *)

let sbexp3_of_svar2 (loc0: loc) (s2v: svar2): sbexp3 option = None
(*
  let s2t = s2v.svar2sort in
    if st2leq s2t st2addr then
      Some (SBE3igte (SIE3var s2v, SIE3int 0))
    else if st2leq s2t st2bool then
      Some (
	SBE3add (
	  SBE3igte (SIE3var s2v, SIE3int 0),
	  SBE3igte (SIE3int 1, SIE3var s2v)
	)
      )
    else None    
*)

(* ****** ****** *)

let pattern_match_is_nonexhaustive_errmsg loc p2tcs =
  begin
    PR.fprintf stderr "%a: nonexhaustive pattern match: %a\n"
      Loc.fprint loc fprint_patcst2_list p2tcs;
    Err.abort ();
 end

let pattern_match_is_nonexhaustive_warnmsg loc p2tcs =
  begin
    PR.fprintf stderr "%a: nonexhaustive pattern match: %a\n"
      Loc.fprint loc fprint_patcst2_list p2tcs;
  end

(* ****** ****** *)

let rec cstr3_solve
  (s2vs: svar2 list) (s3bes: sbexp3 list) (c3t: cstr3): unit =
(*
  let () = PR.fprintf stdout "cstr3_solve: s2vs = %a\n" fprint_svar2_list s2vs in
  let () = PR.fprintf stdout "cstr3_solve: s3bes = %a\n" fprint_sbexp3_list s3bes in
  let () = PR.fprintf stdout "cstr3_solve: c3t = %a\n" fprint_cstr3 c3t in
*)
  let loc0 = c3t.cstr3_loc in
  let () = fundefs_push () in
  let () =
    try match c3t.cstr3_node with
      | CSTR3prop s2p -> cstr3_solve_prop loc0 s2vs s3bes s2p
      | CSTR3itms s3is -> cstr3_solve_itms loc0 s2vs s3bes s3is
    with UnsolvedConstraint (s3bes, s2e) -> begin
      match c3t.cstr3_kind with
	| CK_fatal_error -> begin
	    PR.fprintf stderr "%a: cstr3_solve: unsolved constraint: %a\n"
	      Loc.fprint loc0 fprint_cstr3 c3t;
	    Err.abort ();
	  end
	| CK_nonexhaustive_pattern_match (i, p2tcs) -> begin match i with
	    | 0 -> pattern_match_is_nonexhaustive_warnmsg loc0 p2tcs
	    | 1 -> pattern_match_is_nonexhaustive_errmsg loc0 p2tcs
	    | _ -> ()
	  end
    end in
  let () = fundefs_pop () in ()
(* end of [cstr3_solve] *)

and cstr3_solve_prop loc0
  (s2vs: svar2 list) (s3bes: sbexp3 list) (s2p: sexp2): unit =
(*
  let () =
    PR.fprintf stdout "cstr3_solve_prop: s2vs = %a\n" fprint_svar2_list s2vs in
  let () =
    PR.fprintf stdout "cstr3_solve_prop: s3bes = %a\n" fprint_sbexp3_list s3bes in
  let () =
    PR.fprintf stdout "cstr3_solve_prop: s2p = %a\n" fprint_sexp2 s2p in
*)
  solve_fm loc0 s2vs s3bes s2p
(* end of [cstr3_solve_prop] *)

and cstr3_solve_itms loc0
  (s2vs: svar2 list) (s3bes: sbexp3 list) (s3is: sitem3 list): unit =
(*
  let () =
    PR.fprintf stdout "cstr3_solve_itms: s2vs = %a\n" fprint_svar2_list s2vs in
  let () =
    PR.fprintf stdout "cstr3_solve_itms: s3bes = %a\n" fprint_sbexp3_list s3bes in
  let () =
    PR.fprintf stdout "cstr3_solve_itms: s3is = %a\n" fprint_sitem3_list s3is in
*)
  match s3is with
    | [] -> ()
    | s3i :: s3is -> begin match s3i with
	| SI3cstr c3t ->
	    let () = cstr3_solve s2vs s3bes c3t in
	      cstr3_solve_itms loc0 s2vs s3bes s3is

	| SI3cstr_ref c3t_r ->
	    let () = match !c3t_r with
	      | Some c3t -> cstr3_solve s2vs s3bes c3t | None -> () in
	      cstr3_solve_itms loc0 s2vs s3bes s3is

	| SI3disj s3iss_disj ->
	    cstr3_solve_disj loc0 s2vs s3bes s3iss_disj s3is

	| SI3hypo h3p ->
	    let () = SB.push () in
	    let s3bes = match sbexp3_of_hypo3 h3p with
	      | None ->
(*
		  let () =
		    PR.fprintf stderr "unused hypothesis: %a\n" fprint_hypo3 h3p in
*)
		    s3bes
	      | Some s3be -> s3be :: s3bes in
	    let () = cstr3_solve_itms loc0 s2vs s3bes s3is in
	    let () = SB.pop () in ()

	| SI3svar s2v ->
	    cstr3_solve_itms loc0 (s2v :: s2vs) s3bes s3is

	| SI3sVar s2V -> cstr3_solve_itms loc0 s2vs s3bes s3is
(*
	    begin
	      PR.fprintf stderr "%a: cstr3_solve_itms: s2V = <%a>\n"
		Loc.fprint loc0 fprint_sVar2 s2V;
	      Err.abort ()
	    end
*)
      end
(* end of [cstr3_solve_itms] *)

and cstr3_solve_disj loc0
  (s2vs: svar2 list) (s3bes: sbexp3 list)
  (s3iss_disj: sitem3 list list) (s3is: sitem3 list): unit =
  match s3iss_disj with
    | s3is_disj :: s3iss_disj -> begin
        let () = fundefs_push () in
        let () = cstr3_solve_itms loc0 s2vs s3bes (s3is_disj @ s3is) in
	let () = fundefs_pop () in
	  cstr3_solve_disj loc0 s2vs s3bes s3iss_disj s3is
      end
    | [] -> ()
(* end of [cstr3_solve_disj] *)

let cstr3_solve_init (c3t: cstr3): unit =
(*
  let () =
    PR.fprintf stdout
      "cstr3_solve_init: SB.depth () = %i\n" (SB.depth ()) in
*)
  let () = (SB.initialize (); fundefs_init ()) in
    cstr3_solve [] [] c3t
(* end of [cstr3_solve_init] *)

(* ****** ****** *)

(* end of [ats_constraint.ml] *)
