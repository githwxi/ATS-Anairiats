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

open Ats_syntax
open Ats_staexp1
open Ats_dynexp1
open Ats_errmsg1

(* ****** ****** *)

module BI = Big_int
module PR = Printf

module Eff = Ats_effect
module Err = Ats_error
module Fil = Ats_filename
module Fix = Ats_fixity
module Loc = Ats_location
module Par = Ats_parser
module Sym = Ats_symbol

module Env1 = Ats_env1

(* ****** ****** *)

type loc = Loc.location

let error (s: string): 'a = begin
  prerr_string "ats_trans1: "; Err.error s;
end (* end of [error_with] *)

let error_with_loc (loc: loc) (s: string): 'a = begin
  prerr_string "ats_trans1: "; Err.error_with_loc loc s;
end (* end of [error_with_loc] *)

(* ****** ****** *)

(* recording statically loaded files *)

let staloadedFileMap: (trans1_res Sym.SymMap.t) ref = ref (Sym.SymMap.empty)

let staloadedFileMapAdd (g: symbol) (res: trans1_res): unit =
  staloadedFileMap := Sym.SymMap.add g res !staloadedFileMap

let staloadedFileMapFind (g: symbol): trans1_res option =
  Sym.sym_find g !staloadedFileMap

(* recording dynamically loaded files *)

let dynloadedFileMap: (trans1_res Sym.SymMap.t) ref = ref (Sym.SymMap.empty)

let dynloadedFileMapAdd (g: symbol) (res: trans1_res): unit =
  dynloadedFileMap := Sym.SymMap.add g res !dynloadedFileMap

let dynloadedFileMapFind (g: symbol): trans1_res option =
  Sym.sym_find g !dynloadedFileMap

(* ****** ****** *)

type e0xp1_item = e0xp1 Fix.item

let app_e0xp1_item : e0xp1_item =
  let f (e1: e0xp1) (e2: e0xp1): e0xp1_item =
    let loc = Loc.combine e1.e0xp1_loc e2.e0xp1_loc in
    let es2: e0xp1 list = match e2.e0xp1_node with
      | E0XP1list es -> es
      | _ -> [e2] in
      Fix.Atm (e0xp1_app loc e1 es2) in
    Fix.app_item f
(* end of [app_e0xp1_item] *)

let make_e0xp1opr : e0xp1 -> Fix.fixity -> e0xp1_item =
  Fix.make_opr (function s -> s.e0xp1_loc) e0xp1_app

let rec e0xp_tr (e: e0xp): e0xp1 =
  let rec to_item (e: e0xp): e0xp1_item =
    let loc = e.e0xp_loc in match e.e0xp_node with
      | E0XPapp _ -> Fix.Atm (Fix.resolve loc app_e0xp1_item (to_items e))
      | E0XPchar c -> Fix.Atm (e0xp1_char loc c) 
      | E0XPfloat f (*string*) -> Fix.Atm (e0xp1_float loc f) 
      | E0XPid id -> begin match Env1.fixity_find_opr id with
	  | None -> Fix.Atm (e0xp1_id loc id)
	  | Some f -> make_e0xp1opr (e0xp1_id loc id) f
	end
      | E0XPint i (*intinf*) -> Fix.Atm (e0xp1_int loc i)
      | E0XPlist (es) -> Fix.Atm (e0xp1_list loc (e0xp_list_tr es))
      | E0XPstr s -> Fix.Atm (e0xp1_str loc s)

  and to_items (e: e0xp): e0xp1_item list =
    let rec aux (e: e0xp) (res: e0xp1_item list): e0xp1_item list =
      match e.e0xp_node with
	| E0XPapp (e1, e2) -> aux e1 (to_item e2 :: res)
	| _ -> to_item e :: res in
      aux e [] in
    match to_item e with
      | Fix.Atm e -> e
      | Fix.Opr _ -> e0xp_tr_errmsg e.e0xp_loc
(* end of [e0xp_tr] *)

and e0xp_list_tr (es: e0xp list): e0xp1 list = List.map e0xp_tr es

(* evaluating expressions of the type e0xp *)

let rec e0xp1_eval (e: e0xp1): v0al1 =
(*
  let () = PR.printf "e0xp1_eval: e = %a\n" fprint_e0xp1 e in
*)
  match e.e0xp1_node with
    | E0XP1app (e, es) -> begin
	match e.e0xp1_node with
	  | E0XP1id id -> e0xp1_eval_appid (e.e0xp1_loc) id es
	  | _ -> e0xp1_eval_errmsg_app e.e0xp1_loc
      end
    | E0XP1char c -> V0AL1char c
    | E0XP1float f -> V0AL1float (float_of_string f)
    | E0XP1id id -> begin
	match Env1.e0xp1_find_id id with
	  | Some e -> e0xp1_eval e
	  | None -> e0xp1_eval_errmsg_id e.e0xp1_loc id
      end
    | E0XP1int i -> V0AL1int i
    | E0XP1list es -> begin match es with
      | [e] -> e0xp1_eval e | _ -> e0xp1_eval_errmsg_list e.e0xp1_loc
      end (* end of [E0XP1list] *)
    | E0XP1str s -> V0AL1str s
(* end of [e0xp1_eval] *)

and e0xp1_eval_appid (loc: loc) (id: id) (es: e0xp1 list): v0al1 =
  let s = sym_of_id id in
    if Sym.eq s Sym.symDEFINED then
      match es with
	| [e] -> e0xp1_eval_defined loc e
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symUNDEFINED then
      match es with
	| [e] -> e0xp1_eval_undefined loc e
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symADD then
      match es with
	| [e1; e2] -> e0xp1_eval_add loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symSUB then
      match es with
	| [e1; e2] -> e0xp1_eval_sub loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symMUL then
      match es with
	| [e1; e2] -> e0xp1_eval_mul loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symDIV then
      match es with
	| [e1; e2] -> e0xp1_eval_div loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symLT then
      match es with
	| [e1; e2] -> e0xp1_eval_lt loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symLTE then
      match es with
	| [e1; e2] -> e0xp1_eval_lte loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symGT then
      match es with
	| [e1; e2] -> e0xp1_eval_gt loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symGTE then
      match es with
	| [e1; e2] -> e0xp1_eval_gte loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symEQ then
      match es with
	| [e1; e2] -> e0xp1_eval_eq loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symLTGT then
      match es with
	| [e1; e2] -> e0xp1_eval_neq loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symAND then
      match es with
	| [e1; e2] -> e0xp1_eval_and loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else if Sym.eq s Sym.symOR then
      match es with
	| [e1; e2] -> e0xp1_eval_or loc e1 e2
	| _ -> e0xp1_eval_appid_errmsg_arity loc
    else e0xp1_eval_appid_errmsg_id loc id
(* end of [e0xp1_eval_appid] *)

and e0xp1_eval_defined loc e = begin
  match e.e0xp1_node with
    | E0XP1id id -> begin
	match Env1.e0xp1_find_id id with
	  | Some _ -> v0al1_true | None -> v0al1_false
      end
    | _ -> e0xp1_eval_oper_errmsg loc
end (* end of [e0xp1_eval_defined] *)

and e0xp1_eval_undefined loc e = begin
  match e.e0xp1_node with
    | E0XP1id id -> begin
	match Env1.e0xp1_find_id id with
	  | Some _ -> v0al1_false | None -> v0al1_true
      end
    | _ -> e0xp1_eval_oper_errmsg loc
end (* end of [e0xp1_eval_undefined] *)

and e0xp1_eval_add loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 -> V0AL1float (f1 +. f2)
      | V0AL1int i1, V0AL1int i2 -> V0AL1int (BI.add_big_int i1 i2)
      | V0AL1str s1, V0AL1str s2 -> V0AL1str (s1 ^ s2)
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_add] *)

and e0xp1_eval_sub loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 -> V0AL1float (f1 -. f2)
      | V0AL1int i1, V0AL1int i2 -> V0AL1int (BI.sub_big_int i1 i2)
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_sub] *)

and e0xp1_eval_mul loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 -> V0AL1float (f1 *. f2)
      | V0AL1int i1, V0AL1int i2 -> V0AL1int (BI.mult_big_int i1 i2)
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_mul] *)

and e0xp1_eval_div loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 -> V0AL1float (f1 /. f2)
      | V0AL1int i1, V0AL1int i2 -> V0AL1int (BI.div_big_int i1 i2)
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_div] *)

and e0xp1_eval_lt loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 ->
	  if f1 < f2 then v0al1_true else v0al1_false
      | V0AL1int i1, V0AL1int i2 ->
	  if intinf_lt i1 i2 then v0al1_true else v0al1_false
      | V0AL1str s1, V0AL1str s2 ->
	  if s1 < s2 then v0al1_true else v0al1_false
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_lt] *)

and e0xp1_eval_lte loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 ->
	  if f1 <= f2 then v0al1_true else v0al1_false
      | V0AL1int i1, V0AL1int i2 ->
	  if intinf_lte i1 i2 then v0al1_true else v0al1_false
      | V0AL1str s1, V0AL1str s2 ->
	  if s1 <= s2 then v0al1_true else v0al1_false
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_lte] *)

and e0xp1_eval_gt loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 ->
	  if f1 > f2 then v0al1_true else v0al1_false
      | V0AL1int i1, V0AL1int i2 ->
	  if intinf_gt i1 i2 then v0al1_true else v0al1_false
      | V0AL1str s1, V0AL1str s2 ->
	  if s1 > s2 then v0al1_true else v0al1_false
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_gt] *)

and e0xp1_eval_gte loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 ->
	  if f1 >= f2 then v0al1_true else v0al1_false
      | V0AL1int i1, V0AL1int i2 ->
	  if intinf_gte i1 i2 then v0al1_true else v0al1_false
      | V0AL1str s1, V0AL1str s2 ->
	  if s1 >= s2 then v0al1_true else v0al1_false
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_gte] *)

and e0xp1_eval_eq loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 ->
	  if f1 = f2 then v0al1_true else v0al1_false
      | V0AL1int i1, V0AL1int i2 ->
	  if intinf_eq i1 i2 then v0al1_true else v0al1_false
      | V0AL1str s1, V0AL1str s2 ->
	  if s1 = s2 then v0al1_true else v0al1_false
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_eq] *)

and e0xp1_eval_neq loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1float f1, V0AL1float f2 ->
	  if f1 <> f2 then v0al1_true else v0al1_false
      | V0AL1int i1, V0AL1int i2 ->
	  if intinf_neq i1 i2 then v0al1_true else v0al1_false
      | V0AL1str s1, V0AL1str s2 ->
	  if s1 <> s2 then v0al1_true else v0al1_false
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_neq] *)

and e0xp1_eval_and loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1int i1, V0AL1int i2 ->
	  if intinf_is_zero i1 then v0al1_false
	  else if intinf_is_zero i2 then v0al1_false
	  else v0al1_true 
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_and] *)

and e0xp1_eval_or loc e1 e2 =
  let v1 = e0xp1_eval e1 in
  let v2 = e0xp1_eval e2 in
    match v1, v2 with
      | V0AL1int i1, V0AL1int i2 ->
	  if intinf_is_zero i1 then
	    if intinf_is_zero i2 then v0al1_false else v0al1_true
	  else v0al1_true
      | _, _ -> e0xp1_eval_oper_errmsg loc
(* end of [e0xp1_eval_or] *)

(* ****** ****** *)

type srt1_item = srt1 Fix.item

let app_srt1_item : srt1_item =
  let f (s1t1: srt1) (s1t2: srt1): srt1_item =
    let loc = Loc.combine s1t1.srt1_loc s1t2.srt1_loc in
    let s1ts2: srt1 list = match s1t2.srt1_node with
      | SRT1list s1ts -> s1ts
      | _ -> [s1t2] in
      Fix.Atm (srt1_app loc s1t1 s1ts2) in
    Fix.app_item f
(* end of [app_srt1_item] *)

let make_srt1opr : srt1 -> Fix.fixity -> srt1_item =
  Fix.make_opr (function s -> s.srt1_loc) srt1_app

let rec srt_tr (st: srt): srt1 =
  let rec to_item (st: srt): srt1_item =
    let loc = st.srt_loc in
      match st.srt_node with
	| SRTapp _ -> Fix.Atm (Fix.resolve loc app_srt1_item (to_items st))
	| SRTid id -> begin match Env1.fixity_find_srt_opr id with
	    | None -> Fix.Atm (srt1_id loc id)
	    | Some f -> make_srt1opr (srt1_id loc id) f
	  end
	| SRTlist (sts) -> Fix.Atm (srt1_list loc (srt_list_tr sts))
	| SRTqid qid -> Fix.Atm (srt1_qid loc qid)
	| SRTtup (sts) -> Fix.Atm (srt1_tup loc (srt_list_tr sts))

  and to_items (st: srt): srt1_item list =
    let rec aux (st: srt) (res: srt1_item list): srt1_item list =
      match st.srt_node with
	| SRTapp (st1, st2) -> aux st1 (to_item st2 :: res)
	| _ -> to_item st :: res in
      aux st [] in
    match to_item st with
      | Fix.Atm s1t ->
(*
	  let () = PR.fprintf stdout "srt_tr: %a\n" fprint_srt1 s1t in
*)
	    s1t
      | Fix.Opr _ -> srt_tr_errmsg_opr st.srt_loc
(* end of [srt_tr] *)

and srt_list_tr (sts: srt list): srt1 list = List.map srt_tr sts
and srt_opt_tr (ost: srt option): srt1 option = opt_map srt_tr ost

(* ****** ****** *)

type sexp1_item = sexp1 Fix.item

let app_sexp1_item : sexp1_item =
  let f (s1e1: sexp1) (s1e2: sexp1): sexp1_item =
    let loc = Loc.combine s1e1.sexp1_loc s1e2.sexp1_loc in
    let s1es2: sexp1 list = match s1e2.sexp1_node with
      | SE1list (npf, s1es) -> s1es | _ -> [s1e2] in
      Fix.Atm (sexp1_app loc s1e1 s1es2) in
    Fix.app_item f
(* end of [static_app_sexp1_item] *)

let backslash_sexp1_opr : sexp1_item =
  Fix.make_backslash_opr (function s1e -> s1e.sexp1_loc) sexp1_app
(* end of [static_backslash_sexp1_opr] *)

let static_amper_sexp1_opr (s1e: sexp1): sexp1_item =
  Fix.make_opr
    (function s1e -> s1e.sexp1_loc)
    sexp1_invar_ref s1e Fix.static_amper_fixity
(* end of [static_amper_sexp1_opr] *)

let static_bang_sexp1_opr (s1e: sexp1): sexp1_item =
  Fix.make_opr
    (function s1e -> s1e.sexp1_loc)
    sexp1_invar_val s1e Fix.static_bang_fixity
(* end of [static_bang_sexp1_opr] *)

let static_qmark_sexp1_opr (s1e: sexp1): sexp1_item =
  Fix.make_opr (function s1e -> s1e.sexp1_loc)
    sexp1_top s1e Fix.static_qmark_fixity
(* end of [static_qmark_sexp1_opr] *)

let static_trans_sexp1_opr (s1e: sexp1): sexp1_item =
  Fix.make_opr (function s1e -> s1e.sexp1_loc)
    sexp1_trans s1e Fix.static_trans_fixity
(* end of [static_trans_sexp1_opr] *)

let make_sexp1opr: sexp1 -> Fix.fixity -> sexp1_item =
  Fix.make_opr (function s1e -> s1e.sexp1_loc) sexp1_app

let sarg_tr ((id, ost) : sarg) : sarg1 = (id, srt_opt_tr ost)
let sarg_list_tr (arg: sarg list) : sarg1 list = List.map sarg_tr arg
let sarg_list_list_tr (arg: (sarg list) list): (sarg1 list) list =
  List.map sarg_list_tr arg

let svar_tr ((id, st) : svar) : svar1 = (id, srt_tr st)
let svar_list_tr (svs: svar list) : svar1 list = List.map svar_tr svs
let svar_list_list_tr (svss: (svar list) list): (svar1 list) list =
  List.map svar_list_tr svss

(* ****** ****** *)

let rec sexp_tr (se: sexp): sexp1 =
  let rec to_item (se: sexp): sexp1_item =
    let loc = se.sexp_loc in
      match se.sexp_node with
	| SEann (se, st) ->
	    let s1e = sexp_tr se in
	    let s1t = srt_tr st in
	      Fix.Atm (sexp1_ann loc s1e s1t)
	| SEapp _ -> Fix.Atm (Fix.resolve loc app_sexp1_item (to_items se))
	| SEchar c -> Fix.Atm (sexp1_char loc c)
	| SEexi (sqs, se) -> Fix.Atm (sexp1_exi loc (squas_tr sqs) (sexp_tr se))
	| SEextype name -> Fix.Atm (sexp1_extype loc name)
	| SEid id when sid_is_amper id -> 
	    static_amper_sexp1_opr (sexp1_qid loc (None, id))
	| SEid id when sid_is_backslash id -> backslash_sexp1_opr
	| SEid id when sid_is_bang id ->
	    static_bang_sexp1_opr (sexp1_qid loc (None, id))
	| SEid id when sid_is_qmark id ->
	    static_qmark_sexp1_opr (sexp1_qid loc (None, id)) 
	| SEid id when sid_is_trans id ->
	    static_trans_sexp1_opr (sexp1_qid loc (None, id))
	| SEid id -> begin match Env1.fixity_find_sexp_opr id with
	    | None -> Fix.Atm (sexp1_qid loc (None, id))
	    | Some f -> make_sexp1opr (sexp1_qid loc (None, id)) f
	  end
	| SEimp tags -> begin
	    let (fc, lin, prf, effc) =
	      Eff.efftags_process loc FUNCLOfun(*default*) tags in
	      match Env1.fixity_find_sexp_opr sid_arrow with
		| Some f -> make_sexp1opr (sexp1_imp loc fc lin prf (Some effc)) f
		| None -> sexp_tr_errmsg ()
	  end
	| SEint i -> Fix.Atm (sexp1_int loc i)
	| SElam (arg, ost_res, se_body) ->
	    let arg = sarg_list_tr arg in
	    let os1t_res = srt_opt_tr ost_res in
	    let s1e_body = sexp_tr se_body in
              Fix.Atm (sexp1_lam loc arg os1t_res s1e_body)
	| SElist (npf, ses) -> Fix.Atm (sexp1_list loc npf (sexp_list_tr ses))
	| SEmod (id, lses) ->
	    let ls1es = labsexp_list_tr lses in Fix.Atm (sexp1_mod loc id ls1es)
	| SEop id -> Fix.Atm (sexp1_qid loc (None, id))
	| SEqid (dq, id) -> Fix.Atm (sexp1_qid loc (Some dq, id))
	| SEstruct lses -> Fix.Atm (sexp1_struct loc (labsexp_list_tr lses))
	| SEtyarr (se_elt, sess_dim) ->
	    let s1e_elt = sexp_tr se_elt in
	    let s1ess_dim = List.map sexp_list_tr sess_dim in
	      Fix.Atm (sexp1_tyarr loc s1e_elt s1ess_dim)
	| SEtyrec (is_flat, lses) ->
	    Fix.Atm (sexp1_tyrec loc is_flat (labsexp_list_tr lses))
	| SEtytup (is_flat, (npf, ses)) ->
	    Fix.Atm (sexp1_tytup loc is_flat npf (sexp_list_tr ses))
	| SEuni (sqs, se) -> Fix.Atm (sexp1_uni loc (squas_tr sqs) (sexp_tr se))
	| SEunion (se, lses) ->
	    Fix.Atm (sexp1_union loc (sexp_tr se) (labsexp_list_tr lses))

  and to_items (se: sexp): sexp1_item list =
    let rec aux (se: sexp) (res: sexp1_item list): sexp1_item list =
      match se.sexp_node with
	| SEapp (se1, se2) -> aux se1 (to_item se2 :: res)
	| _ -> to_item se :: res in
      aux se [] in
    match to_item se with
      | Fix.Atm s1e ->
(*
	  let () = PR.fprintf stdout "sexp_tr: %a\n" fprint_sexp1 s1e in
*)
	    s1e
      | Fix.Opr _ -> sexp_tr_errmsg_opr se.sexp_loc
(* end of [sexp_tr] *)

and labsexp_tr ((l, osess1, se2): labsexp): labsexp1 =
  (l, sexp_list_list_opt_tr osess1, sexp_tr se2)

and sexp_list_tr (ses: sexp list): sexp1 list = List.map sexp_tr ses

and sexp_list_list_tr (sess: sexp list list): sexp1 list list =
  List.map sexp_list_tr sess

and sexp_opt_tr (ose: sexp option): sexp1 option =
  match ose with None -> None | Some se -> Some (sexp_tr se)

and sexp_list_opt_tr (oses: (sexp list) option): (sexp1 list) option =
  match oses with None -> None | Some ses -> Some (sexp_list_tr ses)
(* end of [sexp_list_opt_tr] *)

and sexp_list_list_opt_tr (osess: (sexp list list) option)
  : (sexp1 list list) option = match osess with
    | None -> None | Some sess -> Some (sexp_list_list_tr sess)
(* end of [sexp_list_list_opt_tr] *)

and labsexp_list_tr (lses: labsexp list): labsexp1 list =
  List.map labsexp_tr lses

and squa_tr (sq: squa): squa1 = match sq with
  | SQprop se -> SQ1prop (sexp_tr se)
  | SQvars (ids, ste) -> SQ1vars (ids, srtext_tr ste)

and squa_list_tr (sqs: squa list): squa1 list = List.map squa_tr sqs

and squas_tr (sqs: squas): squas1 =
  squas1 sqs.squas_loc (squa_list_tr sqs.squas_node)

and squas_list_tr (sqss: squas list): squas1 list =
  let rec aux s1qss = function
    | [] -> List.rev s1qss
    | sqs :: sqss -> aux (squas_tr sqs :: s1qss) sqss in
    aux [] sqss
(* end of [squas_list_tr] *)

and squas_opt_tr_1 (osqs: squas option): squas1 = match osqs with
  | None -> squas1 Loc.nonloc []
  | Some sqs -> squas1 sqs.squas_loc (squa_list_tr sqs.squas_node)

and squas_opt_tr_2 (osqs: squas option): squas1 option =
  opt_map squas_tr osqs

and srtext_tr (ste: srtext): srtext1 =
  let node: srtext1_node = match ste.srtext_node with
    | STEsrt st -> STE1srt (srt_tr st)
    | STEsub (id, ste, ses) -> STE1sub (id, srtext_tr ste, sexp_list_tr ses) in
    { srtext1_loc= ste.srtext_loc; srtext1_node= node; }
(* end of [srtext_tr] *)

let svararg_tr (sa: svararg): svararg1 =
  match sa with
    | SVARARGone -> SVARARG1one
    | SVARARGall -> SVARARG1all
    | SVARARGseq sas -> SVARARG1seq (sarg_list_tr sas)

let sexparg_tr (sa: sexparg): sexparg1 =
  match sa with
    | SEXPARGone -> SEXPARG1one
    | SEXPARGall -> SEXPARG1all
    | SEXPARGseq ses -> SEXPARG1seq (sexp_list_tr ses)

(* ****** ****** *)

type pat1_item = pat1 Fix.item

let app_pat1_item : pat1_item =
  let f (p1t1: pat1) (p1t2: pat1): pat1_item =
    let loc = Loc.combine p1t1.pat1_loc p1t2.pat1_loc in
    let p1t = match p1t2.pat1_node with
      | PT1list (npf, p1ts2) -> pat1_app_dyn loc p1t1 npf p1ts2
      | PT1svararg sa2 -> begin match p1t1.pat1_node with
	  | PT1app_sta (p1t1, sa2s) -> pat1_app_sta loc p1t1 (sa2s @ [sa2])
	  | _ -> pat1_app_sta loc p1t1 [sa2]
	end
      | _ -> pat1_app_dyn loc p1t1 0 (* arity_p *) [p1t2] in
      Fix.Atm p1t in Fix.app_item f
(* end of [app_pat1_item] *)

let pat1_app_dyn0 loc p1t p1ts =
  pat1_app_dyn loc p1t 0 (* arity_p *) p1ts

let backslash_pat1_item : pat1_item =
  Fix.make_backslash_opr (function p1t -> p1t.pat1_loc) pat1_app_dyn0

let make_pat1opr: pat1 -> Fix.fixity -> pat1_item =
  Fix.make_opr (function p1t -> p1t.pat1_loc) pat1_app_dyn0

let rec pat_tr (pt: pat): pat1 =
  let rec to_item (pt: pat): pat1_item =
    let loc = pt.pat_loc in match pt.pat_node with
      | PTann (pt, se) ->
	  let p1t = pat_tr pt in
	  let s1e = sexp_tr se in
	    Fix.Atm (pat1_ann loc p1t s1e)
      | PTapp _ ->
	  Fix.Atm (Fix.resolve loc app_pat1_item (to_items pt))
      | PTas (id, pt) -> Fix.Atm (pat1_as loc id (pat_tr pt))
      | PTchar c -> Fix.Atm (pat1_char loc c)
      | PTexi (svs, pt) ->
	  let s1vs = svar_list_tr svs in
	  let p1t = pat_tr pt in Fix.Atm (pat1_exi loc s1vs p1t)
      |	PTfree pt -> Fix.Atm (pat1_free loc (pat_tr pt))
      | PTid id when did_is_underscore id -> Fix.Atm (pat1_anys loc)
      | PTid id when did_is_backslash id -> backslash_pat1_item
      | PTid id -> begin
	  match Env1.fixity_find_dexp_opr id with
	    | Some f -> make_pat1opr (pat1_qid loc (None, id)) f
	    | None -> Fix.Atm (pat1_qid loc (None, id))
	end
      | PTint i -> Fix.Atm (pat1_int loc i)
      | PTlist (npf, pts) ->
	  Fix.Atm (pat1_list loc npf (pat_list_tr pts))
      | PTlst pts -> Fix.Atm (pat1_lst loc (pat_list_tr pts))
      | PTop id -> Fix.Atm (pat1_qid loc (None, id))
      | PTqid (dq, id) -> Fix.Atm (pat1_qid loc (Some dq, id))
      | PTrec (is_flat, is_omit, lpts) ->
	  let lp1ts = labpat_list_tr lpts in
	    Fix.Atm (pat1_rec loc is_flat is_omit lp1ts)
      | PTref (id) -> Fix.Atm (pat1_ref loc id)
      | PTrefas (id, pt) -> Fix.Atm (pat1_refas loc id (pat_tr pt))
      | PTsvararg s1a -> Fix.Atm (pat1_svararg loc (svararg_tr s1a))
      | PTstring s -> Fix.Atm (pat1_string loc s)
      | PTtup (is_flat, (npf, pts)) ->
	  Fix.Atm (pat1_tup loc is_flat npf (pat_list_tr pts))

  and to_items (pt: pat): pat1_item list =
    let rec aux (pt: pat) (res: pat1_item list): pat1_item list =
      match pt.pat_node with
	| PTapp (pt1, pt2) -> aux pt1 (to_item pt2 :: res)
	| _ -> to_item pt :: res in
      aux pt [] in
    match to_item pt with
      | Fix.Atm p1t -> p1t
      | Fix.Opr _ -> pat_tr_errmsg_opr pt.pat_loc
(* end of [pat_tr] *)

and labpat_tr ((l, pt): labpat): labpat1 = (l, pat_tr pt)

and pat_list_tr (pts: pat list): pat1 list = List.map pat_tr pts
and labpat_list_tr (lpts: labpat list): labpat1 list = List.map labpat_tr lpts

(* ****** ****** *)

type dexp1_item = dexp1 Fix.item

let app_dexp1_item : dexp1_item =
  let f (d1e1: dexp1) (d1e2: dexp1): dexp1_item =
    let loc = Loc.combine d1e1.dexp1_loc d1e2.dexp1_loc in
    let d1e: dexp1 = match d1e2.dexp1_node with
      | DE1list (npf, d1es2) -> dexp1_app_dyn loc d1e1 npf d1es2
      | DE1sexparg sa2 -> begin match d1e1.dexp1_node with
	  | DE1app_sta (d1e1, sa2s) -> dexp1_app_sta loc d1e1 (sa2s @ [sa2])
	  | _ -> dexp1_app_sta loc d1e1 [sa2]
	end
      | _ -> dexp1_app_dyn loc d1e1 0 [d1e2] in Fix.Atm d1e in
    Fix.app_item f
(* end of [app_dexp1_item] *)

let dexp1_app_dyn0 loc
  (d1e_fun: dexp1) (d1es_arg: dexp1 list): dexp1 =
  dexp1_app_dyn loc d1e_fun 0 (* arity_p *) d1es_arg
(* end of [dexp1_app_dyn0] *)

let backslash_dexp1_item : dexp1_item =
  Fix.make_backslash_opr (function d1e -> d1e.dexp1_loc) dexp1_app_dyn0
(* end of [backslash_dexp1_item] *)

let make_dexp1opr : dexp1 -> Fix.fixity -> dexp1_item =
  Fix.make_opr (function d1e -> d1e.dexp1_loc) dexp1_app_dyn0
(* end of [make_dexp1opr] *)

let rec dexp1_is_metric (d1e: dexp1): bool =
  match d1e.dexp1_node with
    | DE1lam_met _ -> true
    | DE1lam_dyn (_, _, d1e) -> dexp1_is_metric d1e
    | DE1lam_sta_ana (_, d1e) -> dexp1_is_metric d1e
    | DE1lam_sta_syn (_, d1e) -> dexp1_is_metric d1e
    | DE1lam_sta_para (_, d1e) -> dexp1_is_metric d1e
    | _ -> false
(* end of [dexp1_is_metric] *)

(* ****** ****** *)

let dexp1_term_check loc
  (is_metric: bool) (oeffc: Eff.effcst option): unit =
  match oeffc with
    | Some effc ->
	if not (is_metric || Eff.effcst_contain_ntm effc)
	then begin
	  PR.eprintf "%a: a termination metric is missing.\n"
	    Loc.fprint loc;
	  Err.abort ();
	end
    | None -> ()
(* end of [dexp1_term_check] *)

(* ****** ****** *)

let test_mac
  (str: string): bool =
  let n = String.length (str) in
    if n >= 4 then
     if (str.[0] = 'm' && str.[3] = '#') then true else false
    else false
(* end of [test_mac] *)

let dcstextdef_tr
  (ext: string option): dcstextdef = match ext with
  | Some str ->
      let ismac = test_mac (str) in
	if ismac then DCSTEXTDEFsome_mac str else DCSTEXTDEFsome_fun str
    (* end of [Some] *)
  | None -> DCSTEXTDEFnone
(* end of [dcstextdef_tr] *)

(* ****** ****** *)

let rec dexp_tr (de: dexp): dexp1 =
  let rec to_item (de: dexp): dexp1_item =
    let loc = de.dexp_loc in match de.dexp_node with
      | DEann_type (de, se) ->
	  let d1e = dexp_tr de in
	  let s1e = sexp_tr se in
	    Fix.Atm (dexp1_ann_type loc d1e s1e)
      | DEapp _ -> Fix.Atm (Fix.resolve loc app_dexp1_item (to_items de))
      | DEarr (se, des) ->
	  let s1e = sexp_tr se in
	  let d1es = dexp_list_tr des in
	    Fix.Atm (dexp1_arr loc s1e d1es)
      | DEarrsub (de_root, dess_ind) ->
	  let d1e_root = dexp_tr de_root in
	  let d1ess_ind = List.map dexp_list_tr dess_ind in
	    Fix.Atm (dexp1_arrsub loc d1e_root d1ess_ind)
      | DEcase (i, osty, de, cls) ->
	  let osty1 = statype_opt_tr osty in
	  let d1e = dexp_tr de in
	  let c1ls = cla_list_tr cls in
            Fix.Atm (dexp1_case loc i osty1 d1e c1ls)
      | DEchar c -> Fix.Atm (dexp1_char loc c)
      | DEcrypt (knd, de) -> Fix.Atm (dexp1_crypt loc knd (dexp_tr de))
      | DEdelay de -> Fix.Atm (dexp1_delay loc (dexp_tr de))
      | DEdemac de -> Fix.Atm (dexp1_demac loc (dexp_tr de))
      | DEdynload de -> begin
	  let d1e = dexp_tr de in match d1e.dexp1_node with
	    | DE1string name -> Fix.Atm (dexp1_dynload loc (Fil.filename_make name))
	    | _ -> begin
                PR.eprintf "%a: the dynamic expression needs to be a string constant.\n"
		  Loc.fprint d1e.dexp1_loc;
		Err.abort ();                
              end
        end (* end of [DEdynload] *)
      | DEeffmask (eff, de) -> begin
	  let d1e = dexp_tr de in Fix.Atm (dexp1_effmask loc eff d1e)
        end
      | DEempty -> Fix.Atm (dexp1_empty loc)
      | DEenmac de -> Fix.Atm (dexp1_enmac loc (dexp_tr de))
      | DEexi (sa, de) ->
	  let s1a = sexparg_tr sa in
	  let d1e = dexp_tr de in
            Fix.Atm (dexp1_exi loc s1a d1e)
      | DEextval (se, code) ->
	  let s1e = sexp_tr se in
	    Fix.Atm (dexp1_extval loc s1e code)
      | DEfix (name, args, res, oeff, body) ->
	  let oloc = Some loc in
	  let (ofc, lin, oeffc) = match oeff with
	    | Some tags -> begin
		let (fc, lin, _, effc) =
		  Eff.efftags_process loc FUNCLOfun(*default*) tags in
		  (Some fc, lin, Some effc)
	      end
	    | None -> (None, 0, None) in
	  let is_lin = (lin > 0) in
	  let d1e_fun =
	    dexp_lams_dyn_tr oloc ofc is_lin args res oeffc body in
	  let () = dexp1_term_check loc false oeffc in
            Fix.Atm (dexp1_fix loc name d1e_fun)
      | DEfloat f -> Fix.Atm (dexp1_float loc f)
      | DEfold (tc, de) -> Fix.Atm (dexp1_fold loc tc (dexp_tr de))
      | DEfoldat (sas, de) ->
	  let s1as = List.map sexparg_tr sas in
	  let d1e = dexp_tr de in Fix.Atm (dexp1_foldat loc s1as d1e)
      | DEfreeat (sas, de) ->
	  let s1as = List.map sexparg_tr sas in
	  let d1e = dexp_tr de in Fix.Atm (dexp1_freeat loc s1as d1e)
      | DEfor (oinv, (de_init, de_test, de_post), de_body) ->
	  let oinv1 = loopinv_opt_tr oinv in
	  let d1e_init = dexp_tr de_init in
	  let d1e_test = dexp_tr de_test in
	  let d1e_post = dexp_tr de_post in
	  let d1e_body = dexp_tr de_body in
            Fix.Atm (dexp1_for loc oinv1 d1e_init d1e_test d1e_post d1e_body)
      |	DEid id when did_is_backslash id -> backslash_dexp1_item
      | DEid id when sid_is_bang id ->
	  let d1e = dexp1_qid loc (None, id) in
	    make_dexp1opr d1e Fix.dynamic_bang_fixity
      | DEid id -> begin
	  match Env1.fixity_find_dexp_opr id with
	    | Some f -> make_dexp1opr (dexp1_qid loc (None, id)) f
	    | None -> Fix.Atm (dexp1_qid loc (None, id))
	end
      | DEif (osty, de_cond, de_then, ode_else) ->
	  let osty1 = statype_opt_tr osty in
	  let d1e_cond = dexp_tr de_cond in
	  let d1e_then = dexp_tr de_then in
	  let od1e_else = dexp_opt_tr ode_else in
            Fix.Atm (dexp1_if loc osty1 d1e_cond d1e_then od1e_else)
      | DEint (ik, i) -> Fix.Atm (dexp1_int loc ik i)
      | DElam (is_lin0, args, res, oeff, body) -> begin
	  let oloc = Some loc in
	  let (ofc, lin, oeffc) = match oeff with
	    | Some tags -> begin
		let (fc, lin, _(*prf*), effc) =
		  Eff.efftags_process loc FUNCLOfun(*default*) tags in
		let lin = if is_lin0 then 1 else lin in
		  (Some fc, lin, Some effc)
	      end
	    | None -> begin
		let lin = if is_lin0 then 1 else 0 in (None, lin, None)
	      end in
	  let is_lin = (lin > 0) in
	  let de_lam =
	    dexp_lams_dyn_tr oloc ofc is_lin args res oeffc body in
	    Fix.Atm (de_lam)
	end
      | DElampara (arg, ose_res, de_body) -> begin
	  let arg1 = squas_tr arg in
	  let d1e_body = match ose_res with
	    | Some se_res ->
		let loc = Loc.combine se_res.sexp_loc de_body.dexp_loc in
		let d1e_body = dexp_tr de_body in
		let s1e_res = sexp_tr se_res in
		  dexp1_ann_type loc d1e_body s1e_res
	    | None -> dexp_tr de_body in
	    Fix.Atm (dexp1_lam_sta_para loc arg1 d1e_body)
	end
      | DElet (dcs, de_scope) ->
	  let () = Env1.env_push () in
	  let d1cs = dec_list_tr dcs in
	  let d1e_scope = dexp_tr de_scope in
	  let () = Env1.env_pop () in
            Fix.Atm (dexp1_let loc d1cs d1e_scope)
      | DElist (npf, des_elt) ->
	  let d1es_elt = dexp_list_tr des_elt in
	    Fix.Atm (dexp1_list loc npf d1es_elt)
      | DEloopexn i -> Fix.Atm (dexp1_loopexn loc i)
      | DElst des_elt ->
	  let d1es_elt = dexp_list_tr des_elt in
	    Fix.Atm (dexp1_lst loc d1es_elt)
      | DEmod (mids) ->
	  Fix.Atm (dexp1_mod loc (mid_list_tr mids))
      | DEop id -> Fix.Atm (dexp1_qid loc (None, id))

      | DEparse (id, s) ->
(*
	  let () = PR.fprintf stdout "dexp_tr: DEparse: id = %a\n" fprint_id id in
	  let () = PR.fprintf stdout "dexp_tr: DEparse: s = %s\n" s in
*)
	  let s_new =
	    let parser = match Ats_string_parser.parfun_find id with
	      | Some f -> f
	      | None -> begin
		  PR.eprintf "%a: there is no parse function for <%a>\n"
		    Loc.fprint loc fprint_id id;
		  Err.abort ();
		end in
	      match parser s with
		| Some s -> s
		| None -> begin
		    PR.eprintf "%a: illegal string for <%a>\n"
		      Loc.fprint loc fprint_id id;
		    Err.abort ();
		  end in
(*
	  let () = PR.fprintf stdout "dexp_tr: DEparse: s_new = %s\n" s_new in
*)
	  let prompt out = PR.fprintf out "%a: " Loc.fprint loc in
	  let () = Loc.set_the_location loc in
	  let de = Par.parse_dexp_from_string prompt s_new in
          let () = Loc.reset_the_location () in
            Fix.Atm (dexp_tr de)

      | DEptrof de -> Fix.Atm (dexp1_ptrof loc (dexp_tr de))
      | DEqid (dq, id) -> Fix.Atm (dexp1_qid loc (Some dq, id))
      | DEraise (de) -> Fix.Atm (dexp1_raise loc (dexp_tr de))
      | DErec (is_flat, ldes) ->
	  Fix.Atm (dexp1_rec loc is_flat (labdexp_list_tr ldes))
      | DEsel (is_ptr, l, ind) ->
	  let ind = match ind with
	    | Some dess -> Some (dexp_list_list_tr dess)
	    | None -> None in
	  let d1l = { dlab1_lab= l; dlab1_ind= ind } in
	  let f (d1e: dexp1): dexp1_item = 
	    let loc = Loc.combine d1e.dexp1_loc loc in
	      Fix.Atm (dexp1_sel loc is_ptr d1e d1l) in
	    Fix.Opr (Fix.Postfixop (Fix.select_prec, f))
      | DEseq des ->
	  let d1es = dexp_list_tr des in Fix.Atm (dexp1_seq loc d1es)
      | DEsexparg sa -> Fix.Atm (dexp1_sexparg loc (sexparg_tr sa))
      | DEsif (se_cond, de_then, de_else) ->
	  let s1e_cond = sexp_tr se_cond in
	  let d1e_then = dexp_tr de_then in
	  let d1e_else = dexp_tr de_else in
	    Fix.Atm (dexp1_sif loc s1e_cond d1e_then d1e_else)
      | DEstring s -> Fix.Atm (dexp1_string loc s)
      | DEstruct ldes ->
	  let ld1es = labdexp_list_tr ldes in
	    Fix.Atm (dexp1_struct loc ld1es)
      | DEtemplate (id, sess_arg) ->
	  let s1ess_arg = List.map sexp_list_tr sess_arg in
	    Fix.Atm (dexp1_template loc id s1ess_arg)
      | DEtop -> Fix.Atm (dexp1_top loc)
      | DEtrywith (de, cls) ->
	  let d1e = dexp_tr de in
	  let c1ls = cla_list_tr cls in
	    Fix.Atm (dexp1_trywith loc d1e c1ls)
      | DEtup (is_flat, (npf, des)) ->
	  Fix.Atm (dexp1_tup loc is_flat npf (dexp_list_tr des))
      | DEunfold (tc, de) -> Fix.Atm (dexp1_unfold loc tc (dexp_tr de))
      | DEviewat de -> Fix.Atm (dexp1_viewat loc (dexp_tr de))
      | DEwhere (de, dcs) ->
	  let () = Env1.env_push () in
            (* Note that <dcs> is translated first! *)
	  let d1cs = dec_list_tr dcs in
	  let d1e = dexp_tr de in
	  let () = Env1.env_pop () in
            Fix.Atm (dexp1_where loc d1e d1cs)
      | DEwhile (oinv, de_test, de_body) ->
	  let oinv1 = loopinv_opt_tr oinv in
	  let d1e_test = dexp_tr de_test in
	  let d1e_body = dexp_tr de_body in
            Fix.Atm (dexp1_while loc oinv1 d1e_test d1e_body)

  and to_items (de: dexp): dexp1_item list =
    let rec aux (de: dexp) (res: dexp1_item list): dexp1_item list =
      match de.dexp_node with
	| DEapp (de1, de2) -> aux de1 (to_item de2 :: res)
	| _ -> to_item de :: res in
      aux de [] in
    match to_item de with
      | Fix.Atm d1e -> d1e
      | Fix.Opr _ -> dexp_tr_errmsg_opr de.dexp_loc
(* end of [dexp_tr] *)

and dexp_lams_dyn_tr
  (oloc: loc option)
  (ofc: funclo option)
  (is_lin: bool)
  (fargs: farg list)
  (ose_res: sexp option)
  (oeffc: Eff.effcst option)
  (de_body: dexp): dexp1 =
  let rec aux
    (flag: int) (fargs: farg list) (d1e_body: dexp1): dexp1 =
    match fargs with
      | farg :: fargs ->
          let loc = match oloc with
	    | None -> Loc.combine farg.farg_loc d1e_body.dexp1_loc
	    | Some loc -> loc in
	  begin match farg.farg_node with
	    | FARGsta1 sqs -> begin
		let d1e_body = aux flag fargs d1e_body in
		  dexp1_lam_sta_syn loc (squas_tr sqs) d1e_body
	      end
	    | FARGsta2 arg -> begin
		let d1e_body = aux flag fargs d1e_body in
		  dexp1_lam_sta_ana loc (sarg_list_tr arg) d1e_body
	      end
	    | FARGdyn pt -> begin
		let d1e_body = aux (flag+1) fargs d1e_body in
		let d1e_body =
		  if flag > 0 then begin
		    let fc = FUNCLOclo 1 (*cloptr*) in
		      dexp1_ann_funclo (d1e_body.dexp1_loc) d1e_body fc
		  end else begin match ofc with
		    | Some fc -> begin
			dexp1_ann_funclo (d1e_body.dexp1_loc) d1e_body fc
		      end
		    | None -> d1e_body
		  end in
		let p1t = pat_tr pt in dexp1_lam_dyn loc is_lin p1t d1e_body
	      end
	    | FARGmet ses -> begin
		let d1e_body = aux flag fargs d1e_body in
		  dexp1_lam_met loc (sexp_list_tr ses) d1e_body
	      end
	  end
      | [] -> d1e_body in
  let d1e_body: dexp1 = match ose_res with
    | Some se_res ->
	let loc = Loc.combine se_res.sexp_loc de_body.dexp_loc in
	let d1e_body = dexp_tr de_body in
	let s1e_res = sexp_tr se_res in
	  dexp1_ann_type loc d1e_body s1e_res
    | None -> dexp_tr de_body in
  let d1e_body: dexp1 = match oeffc with
    | Some effc ->
	let loc = d1e_body.dexp1_loc in dexp1_ann_effc loc d1e_body effc
    | None -> d1e_body in
    aux 0 fargs d1e_body
(* end of [dexp_lams_dyn_tr] *)

and labdexp_tr ((l, de): labdexp): labdexp1 = (l, dexp_tr de)

and dexp_list_tr (des: dexp list): dexp1 list = List.map dexp_tr des
and dexp_list_list_tr (dess: dexp list list): dexp1 list list =
  List.map dexp_list_tr dess
and dexp_opt_tr (ode: dexp option): dexp1 option = opt_map dexp_tr ode
and labdexp_list_tr (ldes: labdexp list): labdexp1 list =
  List.map labdexp_tr ldes

and cla_tr (cl: cla): cla1 =
   let p1t = pat_tr cl.cla_pat in
   let p1ts = match p1t.pat1_node with
     | PT1list (npf, p1ts) -> p1ts | _ -> [p1t] in
   let gua = dexp_opt_tr cl.cla_gua in
   let d1e = dexp_tr cl.cla_body in
     cla1 cl.cla_loc p1ts gua cl.cla_isseq cl.cla_isneg d1e
(* end of [cla_tr] *)

and cla_list_tr (cls: cla list): cla1 list = List.map cla_tr cls

and statype_tr (sty: statype): statype1 =
  let (sty_qua, sty_bd) = sty in
  let sty1_qua = squas_opt_tr_1 sty_qua in
  let sty1_bd = statype_body_tr sty_bd in
    (sty1_qua, sty1_bd)
(* end of [statype_tr] *)

and statype_opt_tr (osty: statype option): statype1 option =
  match osty with None -> None | Some sty -> Some (statype_tr sty)

and statype_body_tr (sty_bd: statype_body): statype1_body =
  List.map (function (id, ose) -> (id, sexp_opt_tr ose)) sty_bd

and loopinv_tr (inv: loopinv): loopinv1 =
  let qua: squas1 = squas_opt_tr_1 inv.loopinv_qua in
  let met: (sexp1 list) option = match inv.loopinv_met with
    | None -> None
    | Some ses -> Some (sexp_list_tr ses) in
  let arg = statype_body_tr inv.loopinv_arg in
  let res = statype_opt_tr inv.loopinv_res in
    loopinv1 inv.loopinv_loc qua met arg res
(* end of [loopinv_tr] *)

and loopinv_opt_tr (oinv: loopinv option): loopinv1 option =
  match oinv with None -> None | Some inv -> Some (loopinv_tr inv)

(* ****** ****** *)

and prec_tr_error (opr: id): 'a = begin
  prerr_string Err.prompt;
  Loc.prerr (loc_of_id opr);
  prerr_string ": the operator <";
  fprint_id stderr opr;
  prerr_line "> is given no fixity.";
  Err.abort ();
end (* end of [prec_tr_error] *)

and prec_tr (p: prec): Fix.prec = match p with
  | PRECint i -> Fix.prec_of_int (BI.int_of_big_int i)
  | PRECopr (opr) -> begin
      match Env1.fixity_find_opr opr with
	| None -> prec_tr_error opr
	| Some fx -> begin
            match fx with
              | Fix.Nonfix -> prec_tr_error opr
              | Fix.Infix (p, _) -> p
              | Fix.Prefix p -> p
              | Fix.Postfix p -> p
          end
    end
(* end of [prec_tr] *)

and dec_fixity_tr (fx: fixity) (ids: id list): unit =
  let fx: Fix.fixity = match fx with
    | Infix (p, a) -> Fix.Infix (prec_tr p, a)
    | Postfix p -> Fix.Postfix (prec_tr p)
    | Prefix p -> Fix.Prefix (prec_tr p) in
  let rec aux (ids: id list): unit = match ids with
    | [] -> ()
    | id :: ids -> (Env1.fixity_add_opr id fx; aux ids) in
    aux ids
(* end of [dec_fixity_tr] *)

and dec_nonfix_tr (ids: id list): unit =
  let rec aux (ids: id list): unit = match ids with
    | [] -> () | id :: ids -> (Env1.fixity_add_opr id Fix.Nonfix) in
    aux ids
(* end of [dec_nonfix_tr] *)

(* ****** ****** *)

and dec_srtdef_tr (d: dec_srtdef): dec1_srtdef =
  dec1_srtdef d.dec_srtdef_loc
    d.dec_srtdef_name d.dec_srtdef_arg (srtext_tr d.dec_srtdef_def)
(* end of [dec_srtdef_tr] *)

and dec_srtdef_list_tr (ds: dec_srtdef list): dec1_srtdef list =
  List.map dec_srtdef_tr ds

and datsrtcon_tr (c: datsrtcon): datsrtcon1 =
  let s1ts: srt1 list = match c.datsrtcon_arg with
      | None -> []
      | Some st -> let s1t = srt_tr st in
          match s1t.srt1_node with SRT1list s1ts -> s1ts | _ -> [s1t] in
    datsrtcon1 c.datsrtcon_loc c.datsrtcon_name s1ts
(* end of [datsrtcon_tr] *)

and dec_datsrt_tr (d: dec_datsrt): dec1_datsrt =
  let cs = List.map datsrtcon_tr d.dec_datsrt_con in
    match d.dec_datsrt_arg with
      | None -> dec1_datsrt d.dec_datsrt_loc d.dec_datsrt_name [] cs
      | Some arg -> dec1_datsrt d.dec_datsrt_loc d.dec_datsrt_name arg cs
(* end of [dec_datsrt_tr] *)

and dec_datsrt_list_tr (ds: dec_datsrt list): dec1_datsrt list =
  List.map dec_datsrt_tr ds

and datarg_list_tr (xs: datarg list): (sid option * srt1 * int) list =
  let aux = function
    | DATARGsrt (st, i) -> let s1t = srt_tr st in (None, s1t, i)
    | DATARGidsrt (id, (st, i)) -> let s1t = srt_tr st in (Some id, s1t, i) in
    List.map aux xs
(* end of [datarg_list_tr] *)

and dec_stacon_tr (d: dec_stacon): dec1_stacon =
  let loc = d.dec_stacon_loc in
  let name = d.dec_stacon_name in
  let def = sexp_opt_tr d.dec_stacon_def in
    match d.dec_stacon_arg with
      | Some xs ->
	  let arg = datarg_list_tr xs in dec1_stacon loc name (Some arg) def
      | None -> dec1_stacon loc name None def
(* end of [dec_stacon_tr] *)

and dec_stacon_list_tr (ds: dec_stacon list): dec1_stacon list =
  List.map dec_stacon_tr ds

and dec_stacst_tr (d: dec_stacst): dec1_stacst =
  let arg = List.map srt_list_tr d.dec_stacst_arg in
  let s1t = srt_tr d.dec_stacst_sort in
    dec1_stacst d.dec_stacst_loc d.dec_stacst_name arg s1t
(* end of [dec_stacst_tr] *)

and dec_stacst_list_tr (ds: dec_stacst list): dec1_stacst list =
  List.map dec_stacst_tr ds

and dec_stavar_tr (d: dec_stavar): dec1_stavar =
  let s1t = srt_tr d.dec_stavar_sort in
    dec1_stavar d.dec_stavar_loc d.dec_stavar_name s1t
(* end of [dec_stavar_tr] *)

and dec_stavar_list_tr (ds: dec_stavar list): dec1_stavar list =
  List.map dec_stavar_tr ds

and dec_dyncst_tr_aux1 (xs: dfarg0 list): sexp1 list =
  match xs with
    | x :: xs -> begin match x.dfarg0_sexp with
        | Some se -> sexp_tr se :: dec_dyncst_tr_aux1 xs
        | None -> dec_dyncst_tr_aux1_errmsg (x)
      end
    | [] -> []
(* end of [dec_dyncst_tr_aux1] *)

and dec_dyncst_tr_aux2 (is_fun0: bool) (is_prf0: bool)
  (xs: farg0 list) (oeff: efftags option) (s1e_res: sexp1): sexp1 =
(*
  let () =
    PR.fprintf stdout "dec_dyncst_tr_aux2: s1e_res = %a\n"
      fprint_sexp1 s1e_res in
*)
  let loc_res = s1e_res.sexp1_loc in
  let fc0 = FUNCLOfun(*default*) in
  let (fc, lin, prf, oeffc) = match oeff with
    | Some tags -> begin
	let (fc, lin, prf, effc) = Eff.efftags_process loc_res fc0 tags in
	let prf = if is_prf0 then 1 else prf in (fc, lin, prf, Some effc)
      end
    | None -> begin
	let prf = if is_prf0 then 1 else 0 in (fc0, 0, prf, None)
      end in
  let () = match fc with
    | FUNCLOclo knd ->
        if knd >= 0 then begin
          PR.eprintf "%a: a clousure at the toplevel must be a reference"
	    Loc.fprint loc_res;
	  Err.abort ()
        end
    | FUNCLOfun -> () in
  let rec aux
    (flag: int) (xs: farg0 list) (s1e_res: sexp1): int * sexp1 =
    match xs with
      | x :: xs -> begin match x.farg0_node with
        | FARG0dyn (npf, ys) -> begin
	    let s1es_arg =
	      sexp1_list x.farg0_loc npf (dec_dyncst_tr_aux1 ys) in
	    let (n, s1e_res) = aux (flag+1) xs s1e_res in
	    let loc_res = s1e_res.sexp1_loc in
	    let loc = Loc.combine x.farg0_loc loc_res in
	    let fc = if flag > 0 then FUNCLOclo 1 (*cloptr*) else fc in
	    let imp =
	      if n > 0 then begin
		sexp1_imp loc_res fc 0(*lin*) 0(*prf*) None
	      end else begin
		sexp1_imp loc_res fc lin prf oeffc
	      end in
	      (n+1, sexp1_app loc imp [s1es_arg; s1e_res])
	  end
        | FARG0sta sqs -> begin
	    let s1qs = squas_tr sqs in
	    let (n, s1e_res) = aux flag xs s1e_res in
	    let loc_res = s1e_res.sexp1_loc in
            let loc = Loc.combine x.farg0_loc loc_res in
	    let () =
	      if n = 0 then begin
		PR.eprintf
		  "%a: dec_dyncst_tr_aux2: illegal use of effect annotation.\n"
		  Loc.fprint loc_res;
		Err.abort ();
	      end in
              (n, sexp1_uni loc s1qs s1e_res)
	  end
	end
      | [] -> (0, s1e_res) in
  let (n, s1e_res) = aux 0 xs s1e_res in
  let () =
    if (is_fun0 && n = 0) then begin
      PR.eprintf
	"%a: dec_dyncst_tr_aux2: illegal function declaration.\n"
	Loc.fprint loc_res;
      Err.abort ();
    end in
    s1e_res
(* end of [dec_dyncst_tr_aux2] *)

and dec_dyncst_tr
  (is_fun: bool) (is_prf: bool) (d: dec_dyncst): dec1_dyncst =
  let s1e_res = sexp_tr d.dec_dyncst_res in
  let s1e = dec_dyncst_tr_aux2
    is_fun is_prf d.dec_dyncst_arg d.dec_dyncst_eff s1e_res in
  let filename = d.dec_dyncst_filename in
  let extdef = dcstextdef_tr d.dec_dyncst_extdef in
    dec1_dyncst d.dec_dyncst_loc d.dec_dyncst_name filename s1e extdef
(* end of [dec_dyncst_tr] *)

and dec_dyncst_list_tr
  (dck: dcstkind) (ds: dec_dyncst list): dec1_dyncst list =
  let is_fun = dcstkind_is_fun dck in
  let is_prf = dcstkind_is_proof dck in
  List.map (dec_dyncst_tr is_fun is_prf) ds
(* end of [dec_dyncst_list_tr] *)

and dec_sexpdef_tr (d: dec_sexpdef): dec1_sexpdef =
  dec1_sexpdef d.dec_sexpdef_loc d.dec_sexpdef_name
    (sarg_list_list_tr d.dec_sexpdef_arg)
    (srt_opt_tr d.dec_sexpdef_res) (sexp_tr d.dec_sexpdef_def)
(* end of [dec_sexpdef_tr] *)

and dec_sexpdef_list_tr (ds: dec_sexpdef list): dec1_sexpdef list =
  List.map dec_sexpdef_tr ds

and dec_sasp_tr (d: dec_sasp): dec1_sasp =
  dec1_sasp d.dec_sasp_loc d.dec_sasp_name
    (sarg_list_list_tr d.dec_sasp_arg)
    (srt_opt_tr d.dec_sasp_res) (sexp_tr d.dec_sasp_def)
(* end of [dec_sasp_tr] *)

and dec_sasp_list_tr (ds: dec_sasp list): dec1_sasp list =
  List.map dec_sasp_tr ds

and datcon_tr (dtc: datcon): datcon1 =
  let loc = dtc.datcon_loc in
  let name = dtc.datcon_name in
  let qua = squas_list_tr dtc.datcon_qua in
  let npf_s1es_arg = match dtc.datcon_arg with
    | Some se ->  begin
        let s1e = sexp_tr se in match s1e.sexp1_node with
            | SE1list npf_s1es -> npf_s1es | _ -> (0, [s1e])
      end
    | None -> (0, []) in
  let os1es_ind = match dtc.datcon_ind with
    | Some ses -> Some (sexp_list_tr ses) | None -> None in
  datcon1 loc name qua npf_s1es_arg os1es_ind
(* end of [datcon_tr] *)

and datcon_list_tr (cs: datcon list): datcon1 list =
  List.map datcon_tr cs

and dec_dat_tr (d: dec_dat): dec1_dat =
  let arg = match d.dec_dat_arg with
    | None -> None
    | Some xs -> Some (datarg_list_tr xs) in
  let con = datcon_list_tr d.dec_dat_con in
    dec1_dat d.dec_dat_loc d.dec_dat_name d.dec_dat_filename arg con
(* end of [dec_dat_tr] *)

and dec_dat_list_tr (ds: dec_dat list): dec1_dat list =
  List.map dec_dat_tr ds

and dec_exn_tr (d: dec_exn): dec1_exn =
  let qua = squas_list_tr d.dec_exn_qua in
  let npf_s1es_arg = match d.dec_exn_arg with
    | Some se -> begin
        let s1e = sexp_tr se in match s1e.sexp1_node with
          | SE1list npf_s1es -> npf_s1es | _ -> (0, [s1e])
      end
    | None -> (0, []) in
    dec1_exn d.dec_exn_loc d.dec_exn_name d.dec_exn_filename qua npf_s1es_arg
(* end of [dec_exn_tr] *)

and dec_exn_list_tr (ds: dec_exn list): dec1_exn list =
  List.map dec_exn_tr ds

(* ****** ****** *)

and mtitemdec_tr (mtid: mtitemdec): mtitemdec1 =
  match mtid.mtitemdec_node with
    | MTIDsta (id, st) -> mtitemdec1_sta mtid.mtitemdec_loc id (srt_tr st)
    | MTIDval (is_prf, id, arg, eff, res) -> 
	let s1e = dec_dyncst_tr_aux2 false is_prf arg eff (sexp_tr res) in
	  mtitemdec1_val mtid.mtitemdec_loc is_prf id s1e
    | MTIDsexpdefs ds ->
	mtitemdec1_sexpdefs mtid.mtitemdec_loc (dec_sexpdef_list_tr ds)
    | MTIDtypedefs ds ->
	mtitemdec1_typedefs mtid.mtitemdec_loc (dec_sexpdef_list_tr ds)
    | MTIDtypedefrecs ds ->
	mtitemdec1_typedefrecs mtid.mtitemdec_loc (dec_sexpdef_list_tr ds)
(* end of [mtitemdec_tr] *)

and mtitemdec_list_tr (mtids: mtitemdec list): mtitemdec1 list =
  List.map mtitemdec_tr mtids

and dec_modtype_tr (d: dec_modtype): dec1_modtype = {
  dec1_modtype_loc = d.dec_modtype_loc;
  dec1_modtype_name = d.dec_modtype_name;
  dec1_modtype_def = mtitemdec_list_tr (d.dec_modtype_def);
} (* end of [dec_modtype_tr] *)

and dec_modtype_list_tr (ds: dec_modtype list): dec1_modtype list =
  List.map dec_modtype_tr ds

(* ****** ****** *)

and dec_macdef_tr (d: dec_macdef): dec1_macdef =
  dec1_macdef d.dec_macdef_loc d.dec_macdef_name d.dec_macdef_arg
    (dexp_tr d.dec_macdef_def)
(* end of [dec_macdef_tr] *)

and dec_macdef_list_tr (ds: dec_macdef list): dec1_macdef list =
  List.map dec_macdef_tr ds

and dec_var_tr (d: dec_var): dec1_var =
  dec1_var d.dec_var_loc d.dec_var_name
    (sexp_opt_tr d.dec_var_type) (dexp_opt_tr d.dec_var_ini)
(* end of [dec_var_tr] *)

and dec_var_list_tr (ds: dec_var list): dec1_var list =
  List.map dec_var_tr ds

and dec_val_tr (d: dec_val): dec1_val =
  let p1t = pat_tr d.dec_val_pat in
  let d1e = dexp_tr d.dec_val_def in
  let d1e: dexp1 = match d.dec_val_ann with
    | Some (se, st) ->
	let s1e = sexp_tr se in
	let s1t = srt_tr st in
	let s1e = sexp1_ann se.sexp_loc s1e s1t in
	let loc = Loc.combine d1e.dexp1_loc s1e.sexp1_loc in
	  dexp1_ann_type loc d1e s1e
    | None -> d1e in
    dec1_val d.dec_val_loc p1t d1e
(* end of [dec_val_tr] *)

and dec_val_list_tr (ds: dec_val list): dec1_val list =
  List.map dec_val_tr ds

and dec_valpar_list_tr (ds: dec_val list): dec1_val list =
  List.map dec_val_tr ds

and dec_valrec_list_tr (ds: dec_val list): dec1_val list =
  List.map dec_val_tr ds

and dec_fun_tr (fk: funkind) (d: dec_fun): dec1_fun =
  let loc = d.dec_fun_loc in
  let is_prf = funkind_is_proof fk in
  let (oeff, ose_res) = match d.dec_fun_res with
    | Some (oeff, se) -> (oeff, Some se) | None -> (None, None) in
  let (ofc, oeffc) = match oeff with
    | Some tags -> begin
	let (fc, _(*lin*), _(*prf*), effc) =
	  Eff.efftags_process loc FUNCLOfun(*default*) tags in
	  (Some fc, Some effc)
      end
    | None -> begin
	let fc = FUNCLOfun(*default*) in
	let effc =
	  if is_prf then Eff.effcst_nil else Eff.effcst_all in
	  (Some fc, Some effc)
      end in
  let d1e_def =
      dexp_lams_dyn_tr None (*loc*) ofc false (* is_linear *)
	d.dec_fun_arg ose_res oeffc d.dec_fun_body in
  let () =
    if funkind_is_recursive fk then
      dexp1_term_check loc (dexp1_is_metric d1e_def) oeffc in
  let os1e_ann: sexp1 option = match d.dec_fun_ann with
    | Some (se, st) ->
	let s1e = sexp_tr se in let s1t = srt_tr st in
	  Some (sexp1_ann se.sexp_loc s1e s1t)
    | None -> None in
  dec1_fun loc d.dec_fun_name d1e_def os1e_ann
(* end of [dec_fun_tr] *)

and dec_fun_list_tr
  (fk: funkind) (ds: dec_fun list): dec1_fun list =
  List.map (dec_fun_tr fk) ds
(* end of [dec_fun_list_tr] *)

and dec_impl_tr (d: dec_impl): dec1_impl =
  let tmparg = sexp_list_list_tr d.dec_impl_tmparg in
  let body =
    dexp_lams_dyn_tr None (*loc*) None (*fc*) false (*lin*)
      d.dec_impl_arg d.dec_impl_res None d.dec_impl_body in
    dec1_impl d.dec_impl_loc d.dec_impl_name tmparg body
(* end of [dec_impl_tr] *)

and dec_impl_list_tr (ds: dec_impl list): dec1_impl list =
  List.map dec_impl_tr ds

(* ****** ****** *)

and mid_list_tr (mids: moditemdec list): moditemdec1 list =
  let rec aux (res: moditemdec1 list) = function
    | [] -> List.rev res
    | mid :: mids -> begin match mid.moditemdec_node with
	| MIDfixity (fx, xs) ->
	    let () = dec_fixity_tr fx xs in aux res mids

	| MIDnonfix xs ->
	    let () = dec_nonfix_tr xs in aux res mids

	| MIDsexpdefs (ost, xs) ->
	    let os1t = srt_opt_tr ost in
	    let ds1 = dec_sexpdef_list_tr xs in
	    let d1 = moditemdec1_sexpdefs mid.moditemdec_loc os1t ds1 in
	      aux (d1 :: res) mids

	| MIDtypedefrecs xs ->
	    let ds1 = dec_sexpdef_list_tr xs in
	    let d1 = moditemdec1_typedefrecs mid.moditemdec_loc ds1 in
	      aux (d1 :: res) mids

	| MIDvals (vk, xs) ->
	    let ds1 = dec_val_list_tr xs in
	    let d1 = moditemdec1_vals mid.moditemdec_loc vk ds1 in
	      aux (d1 :: res) mids

	| MIDvalrecs xs ->
	    let ds1 = dec_valrec_list_tr xs in
	    let d1 = moditemdec1_valrecs mid.moditemdec_loc ds1 in
	      aux (d1 :: res) mids

	| MIDfuns (fk, srtarg, xs) ->
	    let ds1 = dec_fun_list_tr fk xs in
	    let d1 = moditemdec1_funs mid.moditemdec_loc fk srtarg ds1 in
	      aux (d1 :: res) mids
      end in
    aux [] mids
(* end of [mid_list_tr] *)

(* ****** ****** *)

and dec_list_tr_aux1 (ds: dec list) (res: dec1 list): dec1 list =
  match ds with
    | d :: ds -> dec_list_tr_aux2 d ds res | [] -> res
(* end of [dec_list_tr_aux1] *)

and dec_list_tr_aux2 (d: dec) (ds: dec list) (res: dec1 list)
  : dec1 list = match d.dec_node with

  | DCfixity (fx, ids) -> begin
      dec_fixity_tr fx ids; dec_list_tr_aux1 ds res
    end

  | DCnonfix ids -> begin
      dec_nonfix_tr ids; dec_list_tr_aux1 ds res
    end

  | DCsymintr ids ->
      let d1 = dec1_symintr d.dec_loc ids in
	dec_list_tr_aux1 ds (d1 :: res) 

  | DCsymelim ids ->
      let d1 = dec1_symelim d.dec_loc ids in
	dec_list_tr_aux1 ds (d1 :: res) 

  | DCsrtdefs xs -> 
      let d1 = dec1_srtdefs d.dec_loc (dec_srtdef_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res) 

  | DCdatsrts xs ->
      let d1 = dec1_datsrts d.dec_loc (dec_datsrt_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCstacons (st, xs) ->
      let s1t = srt_tr st in
      let d1 = dec1_stacons d.dec_loc s1t (dec_stacon_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCstacsts xs ->
      let d1 = dec1_stacsts d.dec_loc (dec_stacst_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCstavars xs ->
      let d1 = dec1_stavars d.dec_loc (dec_stavar_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCextype (name, def) ->
      let d1 = dec1_extype d.dec_loc name (sexp_tr def) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCextval (name, def) ->
      let d1 = dec1_extval d.dec_loc name (dexp_tr def) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCdyncsts (dck, sqss, xs) ->
      let s1qss = squas_list_tr sqss in
      let xs = dec_dyncst_list_tr dck xs in
      let d1 = dec1_dyncsts d.dec_loc dck s1qss xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCsexpdefs (ost, xs) ->
      let os1t = srt_opt_tr ost in
      let d1 = dec1_sexpdefs d.dec_loc os1t (dec_sexpdef_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCtypedefrecs xs ->
      let d1 = dec1_typedefrecs d.dec_loc (dec_sexpdef_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCviewtypedefrecs xs ->
      let d1 = dec1_viewtypedefrecs d.dec_loc (dec_sexpdef_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCsasps xs ->
      let d1 = dec1_sasps d.dec_loc (dec_sasp_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCexns xs ->
      let d1 = dec1_exns d.dec_loc (dec_exn_list_tr xs) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCdata (dk, arg, ds1, ds2) ->
      let d1 =
	dec1_data d.dec_loc dk arg
	  (dec_dat_list_tr ds1) (dec_sexpdef_list_tr ds2) in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCe0xpdef (id, e) ->
      let v = match e with
	| None -> e0xp1_true | Some e -> e0xp_tr e in
      let () = Env1.e0xp1_add_id id v in
	dec_list_tr_aux1 ds res

  | DCe0xperr e -> begin
      let e = e0xp_tr e in
      let v = e0xp1_eval e in match v with
	| V0AL1char c -> (PR.eprintf "'%c'" c; Err.abort ())
	| V0AL1float f -> (PR.eprintf "%f" f; Err.abort ())
	| V0AL1int i -> (fprint_intinf stderr i; Err.abort ())
	| V0AL1str s -> (PR.eprintf "%s" s; Err.abort ())
    end

  | DCe0xpprt e -> begin
      let e = e0xp_tr e in
      let v = e0xp1_eval e in
      let () = match v with
        | V0AL1char c -> PR.eprintf "'%c'" c
        | V0AL1float f -> PR.eprintf "%f" f
	| V0AL1int i -> fprint_intinf stderr i
	| V0AL1str s -> PR.eprintf "%s" s in
	dec_list_tr_aux1 ds res
    end

  | DCoverload (name, id) ->
      let d1 = dec1_overload d.dec_loc name id in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCmacdefs (is_simple, xs) ->
      let xs = dec_macdef_list_tr xs in
      let d1 = dec1_macdefs d.dec_loc is_simple xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCmodtypes (is_prop, xs) ->
      let xs = dec_modtype_list_tr xs in
      let d1 = dec1_modtypes d.dec_loc is_prop xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCvars (is_stack, xs) ->
      let xs = dec_var_list_tr xs in
      let d1 = dec1_vars d.dec_loc is_stack xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCvals (vk, xs) ->
      let xs = dec_val_list_tr xs in
      let d1 = dec1_vals d.dec_loc vk xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCvalpars xs ->
      let xs = dec_valpar_list_tr xs in
      let d1 = dec1_valpars d.dec_loc xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCvalrecs xs ->
      let xs = dec_valrec_list_tr xs in
      let d1 = dec1_valrecs d.dec_loc xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCfuns (fk, srtarg, decarg, xs) ->
      let decarg = squas_list_tr decarg in
      let xs = dec_fun_list_tr fk xs in
      let d1 = dec1_funs d.dec_loc fk srtarg decarg xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCimpls (decarg, xs) ->
      let decarg = sarg_list_list_tr decarg in
      let xs = dec_impl_list_tr xs in
      let d1 = dec1_impls d.dec_loc decarg xs in
	dec_list_tr_aux1 ds (d1 :: res)

  | DClocal (dcs1, dcs2) ->
      let () = Env1.env_push () in
      let d1cs1 = dec_list_tr dcs1 in
      let () = Env1.env_push () in
      let d1cs2 = dec_list_tr dcs2 in
      let () = Env1.env_localjoin () in
      let d1 = dec1_local d.dec_loc d1cs1 d1cs2 in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCifthenelse (ed0css) ->
      let rec aux ed0css = match ed0css with
	| (e, d0cs) :: ed0css -> begin
	    let v = e0xp1_eval (e0xp_tr e) in
	      if v0al1_is_zero v then aux ed0css else d0cs
	  end
	| [] -> [] in
      let res = dec_list_tr_aux1 (aux ed0css) res in
	dec_list_tr_aux1 ds res

  | DCinclude (stadyn, f) ->
      let res = dec_include_tr stadyn f res in dec_list_tr_aux1 ds res

  | DCstaload (osid, f) ->
      let (is_loaded, staload_res) = dec_staload_tr f in
      let d1 = dec1_staload d.dec_loc osid f is_loaded staload_res in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCdynload (f) ->
      let d1 = dec1_dynload d.dec_loc f in
	dec_list_tr_aux1 ds (d1 :: res)

  | DCextern (position, code) ->
      let d1 = dec1_extern d.dec_loc position code in
	dec_list_tr_aux1 ds (d1 :: res)
(* end of [dec_list_tr_aux2] *)

and dec_include_tr
  (stadyn: int) (f: Fil.filename) (res: dec1 list) : dec1 list =
  let fname = Fil.filename_fullname f in
  let () = Fil.filename_push f in
  let d0cs = Par.parse_dec_from_file (stadyn = 0) fname in
  let () = Fil.filename_pop () in
(*
  let () = PR.printf "Including %s begins.\n" fname in
*)
  let res = dec_list_tr_aux1 d0cs res in
(*
  let () = PR.printf "Translating %s ends.\n" fname in
*)
    res
(* end of [dec_include_tr] *)

and dec_staload_tr (f: Fil.filename): bool * trans1_res =
  let fname = Fil.filename_fullname f in
  let fsymbol = Sym.make_with_string fname in
    match staloadedFileMapFind fsymbol with
      | None ->
	  let () = Fil.filename_push f in
	  let is_static =
	    Filename.check_suffix (Fil.filename_basename f) "sats" in
	  let d0cs = Par.parse_dec_from_file is_static fname in
	  let () = Fil.filename_pop () in
(*
	  let () = PR.printf "Translating %s begins.\n" fname in
*)
	  let () = Env1.env_save () in
	  let d1cs = dec_list_tr d0cs in
	  let e0xpenv = Env1.E0xpEnv.get_top () in
	  let () = Env1.env_restore () in
(*
	  let () = PR.printf "Translating %s ends.\n" fname in
*)
	  let res =
	    { trans1_res_sta= is_static;
              trans1_res_defs= e0xpenv;
	      trans1_res_decs = d1cs } in
	  let () = staloadedFileMapAdd fsymbol res in
	    (false (*is_loaded*), res)
      | Some res ->
(*
	  let _ = PR.printf "staloaddec0trans: already loaded: %s\n" fullname in
*)
	  (true (*is_loaded*), res)
(* end of [dec_staload_tr] *)

(*

and dec_dynload_tr (f: Fil.filename): bool * trans1_res =
  let fname = Fil.filename_fullname f in
  let fsymbol = Sym.make_with_string fname in
    match dynloadedFileMapFind fsymbol with
      | None ->
	  let () = Fil.filename_push f in
	  let d0cs = Par.parse_dec_from_file false fname in
	  let () = Fil.filename_pop () in
(*
	  let () = PR.printf "Translating %s begins.\n" fname in
*)
	  let () = Env1.env_save () in
	  let d1cs = dec_list_tr d0cs in
	  let e0xpenv = Env1.E0xpEnv.get_top () in
	  let () = Env1.env_restore () in
(*
	  let () = PR.printf "Translating %s ends.\n" fname in
*)
	  let res = { trans1_res_defs= e0xpenv; trans1_res_decs = d1cs } in
	    (false, res)
      | Some res -> (true, res)

*)
	    
and dec_list_tr (ds: dec list): dec1 list =
  List.rev (dec_list_tr_aux1 ds [])

(* ****** ****** *)

let the_dynloadflag = ref 1
let dynloadflag_get () = !the_dynloadflag

(* ****** ****** *)

let initialize (): unit = begin
  staloadedFileMap := Sym.SymMap.empty;
  dynloadedFileMap := Sym.SymMap.empty;
end (* end of [initialize] *)

(* ****** ****** *)

let finalize (): unit = begin
  match Env1.e0xp1_find_sym (Sym.symDYNLOADFLAG) with
    | Some e -> begin
	let v = e0xp1_eval e in
	let flag = if v0al1_is_zero v then 0 else 1 in
	  the_dynloadflag := flag
      end
    | None -> ()
end (* end of [finalize] *)

(* ****** ****** *)

(* end of [ats_trans1.ml] *)
