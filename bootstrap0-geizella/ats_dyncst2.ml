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

module Loc = Ats_location
module DENV = Ats_stadynenv2
module NS = Ats_name_space

(* a standard error reporting functions *)

let error (s: string): 'a = begin
  prerr_string "ats_dyncst2: "; Err.error s;
end

(* ****** ****** *)

type loc = Loc.location

(* ****** ****** *)

let pat2_bool (loc: loc) (b: bool): pat2 = {
  pat2_loc= loc;
  pat2_node= PT2bool b;
  pat2_svs= [];
  pat2_dvs= [];
  pat2_type= None;
} (* end of [pat2_bool] *)

(* ****** ****** *)

let cla2_of_dexp2_if (b: bool) (d2e: dexp2): cla2 =
  let loc = d2e.dexp2_loc in
  let p2t = pat2_bool loc b in
    cla2 loc [p2t] None false false d2e
(* end of [cla2_of_dexp2_if] *)

let cla2_of_dexp2_if_opt (b: bool) (od2e: dexp2 option): cla2 =
  let d2e = match od2e with
    | None -> dexp2_empty Loc.nonloc | Some d2e -> d2e in
    cla2_of_dexp2_if b d2e
(* end of [cla2_of_dexp2_if_opt] *)

(* ****** ****** *)

let fun_main_name = Sym.make_with_string "main"
let dcst2_fun_main_is_implemented (): bool =
  match DENV.DEXP2env.find_in_pervasives fun_main_name with
    | Some (DI2cst d2c) -> begin
	match d2c.dcst2_def with Some _ -> true | None -> false
      end
    | _ -> error "dcst2_fun_main"
(* end of [dcon2_fun_main_is_implemented] *)

let fun_main_dummy_name = Sym.make_with_string "main_dummy"
let dcst2_fun_main_dummy_is_implemented (): bool =
  match DENV.DEXP2env.find_in_pervasives fun_main_dummy_name with
    | Some (DI2cst d2c) -> begin
	match d2c.dcst2_def with Some _ -> true | None -> false
      end
    | _ -> error "dcst2_fun_main_dummy"
(* end of [dcon2_fun_main_dummy] *)

(* ****** ****** *)

let bool_true_name = Sym.make_with_string "true"
let dcst2_is_bool_true (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in Sym.eq name bool_true_name

let bool_false_name = Sym.make_with_string "false"
let dcst2_is_bool_false (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in Sym.eq name bool_false_name

(* ****** ****** *)

let list_nil_name = Sym.make_with_string "list_nil"
let dcon2_list_nil (): dcon2 =
  match DENV.DEXP2env.find_in_pervasives list_nil_name with
    | Some (DI2con [d2c]) -> d2c
    | _ -> error "dcon2_list_nil"
(* end of [dcon2_list_nil] *)

let list_cons_name = Sym.make_with_string "list_cons"
let dcon2_list_cons (): dcon2 =
  match DENV.DEXP2env.find_in_pervasives list_cons_name with
    | Some (DI2con [d2c]) -> d2c
    | _ -> error "dcon2_list_cons"
(* end of [dcon2_list_cons] *)

(* ****** ****** *)

let lazy_delay_name = Sym.make_with_string "lazy_delay"
let lazy_force_name = Sym.make_with_string "lazy_force"

let dcst2_lazy_delay (): dcst2 =
  match DENV.DEXP2env.find_in_pervasives lazy_delay_name with
    | Some (DI2cst d2c) -> d2c
    | _ -> error "lazy_delay_name"
(* end of [dcst2_lazy_delay] *)

let dcst2_lazy_force (): dcst2 =
  match DENV.DEXP2env.find_in_pervasives lazy_force_name with
    | Some (DI2cst d2c) -> d2c
    | _ -> error "lazy_force_name"
(* end of [dcst2_lazy_force] *)

(* ****** ****** *)

let thunkvalue_thunk_name = Sym.make_with_string "thunkvalue_thunk"

let dcon2_thunkvalue_thunk (): dcon2 =
  match DENV.DEXP2env.find_in_pervasives thunkvalue_thunk_name with
    | Some (DI2con [d2c]) -> d2c
    | _ -> error "dcon2_thunkvalue_thunk"
(* end of [dcon2_thunkvalue_thunk] *)

let thunkvalue_vt_thunk_name = Sym.make_with_string "thunkvalue_vt_thunk"

let dcon2_thunkvalue_vt_thunk (): dcon2 =
  match DENV.DEXP2env.find_in_pervasives thunkvalue_vt_thunk_name with
    | Some (DI2con [d2c]) -> d2c
    | _ -> error "dcon2_thunkvalue_vt_thunk"
(* end of [dcon2_thunkvalue_vt_thunk] *)

(* ****** ****** *)

let sizeof_name = Sym.make_with_string "sizeof"

let dcst2_is_sizeof (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name sizeof_name
(* end of [dcst2_is_sizeof] *)

let dcst2_sizeof (): dcst2 =
  match DENV.DEXP2env.find_in_pervasives sizeof_name with
    | Some (DI2cst d2c) -> d2c | _ -> error "dcst2_sizeof"
(* end of [dcst2_sizeof] *)

(* ****** ****** *)

(* brackets overloading can be extended *)
let dsym2_brackets (loc: Loc.location): dsym2 =
  match DENV.DEXP2env.find Sym.symBRACKETS with
    | Some (DI2sym d2is) ->
	dsym2_make loc (None, Syn.did_brackets) d2is
    | _ -> begin match NS.dexp2_env_find Sym.symBRACKETS with
	| Some (DI2sym d2is) -> dsym2_make loc (None, Syn.did_brackets) d2is
	| _ -> error_of_deadcode "ats_dyncst2: dsym2_brackets"
      end
(* end of [dsym2_brackets] *)

(* ****** ****** *)

let add_bool0_bool0_name = Sym.make_with_string "add_bool0_bool0"
let sub_bool0_bool0_name = Sym.make_with_string "sub_bool0_bool0"
let mul_bool0_bool0_name = Sym.make_with_string "mul_bool0_bool0"
let lt_bool0_bool0_name = Sym.make_with_string "lt_bool0_bool0"
let lte_bool0_bool0_name = Sym.make_with_string "lte_bool0_bool0"
let gt_bool0_bool0_name = Sym.make_with_string "gt_bool0_bool0"
let gte_bool0_bool0_name = Sym.make_with_string "gte_bool0_bool0"
let eq_bool0_bool0_name = Sym.make_with_string "eq_bool0_bool0"
let neq_bool0_bool0_name = Sym.make_with_string "neq_bool0_bool0"

let neg_bool0_name = Sym.make_with_string "neg_bool0"

(* ****** ****** *)

let add_bool1_bool1_name = Sym.make_with_string "add_bool1_bool1"
let sub_bool1_bool1_name = Sym.make_with_string "sub_bool1_bool1"
let mul_bool1_bool1_name = Sym.make_with_string "mul_bool1_bool1"
let lt_bool1_bool1_name = Sym.make_with_string "lt_bool1_bool1"
let lte_bool1_bool1_name = Sym.make_with_string "lte_bool1_bool1"
let gt_bool1_bool1_name = Sym.make_with_string "gt_bool1_bool1"
let gte_bool1_bool1_name = Sym.make_with_string "gte_bool1_bool1"
let eq_bool1_bool1_name = Sym.make_with_string "eq_bool1_bool1"
let neq_bool1_bool1_name = Sym.make_with_string "neq_bool1_bool1"

let neg_bool1_name = Sym.make_with_string "neg_bool1"

(* ****** ****** *)

let lt_char0_char0_name = Sym.make_with_string "lt_char0_char0"
let lte_char0_char0_name = Sym.make_with_string "lte_char0_char0"
let gt_char0_char0_name = Sym.make_with_string "gt_char0_char0"
let gte_char0_char0_name = Sym.make_with_string "gte_char0_char0"
let eq_char0_char0_name = Sym.make_with_string "eq_char0_char0"
let neq_char0_char0_name = Sym.make_with_string "neq_char0_char0"

let lt_char1_char1_name = Sym.make_with_string "lt_char1_char1"
let lte_char1_char1_name = Sym.make_with_string "lte_char1_char1"
let gt_char1_char1_name = Sym.make_with_string "gt_char1_char1"
let gte_char1_char1_name = Sym.make_with_string "gte_char1_char1"
let eq_char1_char1_name = Sym.make_with_string "eq_char1_char1"
let neq_char1_char1_name = Sym.make_with_string "neq_char1_char1"

(* ****** ****** *)

let add_double_double_name = Sym.make_with_string "add_double_double"
let sub_double_double_name = Sym.make_with_string "sub_double_double"
let mul_double_double_name = Sym.make_with_string "mul_double_double"
let div_double_double_name = Sym.make_with_string "div_double_double"
let mod_double_double_name = Sym.make_with_string "mod_double_double"
let lt_double_double_name = Sym.make_with_string "lt_double_double"
let lte_double_double_name = Sym.make_with_string "lte_double_double"
let gt_double_double_name = Sym.make_with_string "gt_double_double"
let gte_double_double_name = Sym.make_with_string "gte_double_double"
let eq_double_double_name = Sym.make_with_string "eq_double_double"
let neq_double_double_name = Sym.make_with_string "neq_double_double"

let neg_double_name = Sym.make_with_string "neg_double"

(* ****** ****** *)

let add_float_float_name = Sym.make_with_string "add_float_float"
let sub_float_float_name = Sym.make_with_string "sub_float_float"
let mul_float_float_name = Sym.make_with_string "mul_float_float"
let div_float_float_name = Sym.make_with_string "div_float_float"
let mod_float_float_name = Sym.make_with_string "mod_float_float"
let lt_float_float_name = Sym.make_with_string "lt_float_float"
let lte_float_float_name = Sym.make_with_string "lte_float_float"
let gt_float_float_name = Sym.make_with_string "gt_float_float"
let gte_float_float_name = Sym.make_with_string "gte_float_float"
let eq_float_float_name = Sym.make_with_string "eq_float_float"
let neq_float_float_name = Sym.make_with_string "neq_float_float"

let neg_float_name = Sym.make_with_string "neg_float"

(* ****** ****** *)

let iadd_name = Sym.make_with_string "iadd"
let isub_name = Sym.make_with_string "isub"
let imul_name = Sym.make_with_string "imul"
let nmul_name = Sym.make_with_string "nmul"
let idiv_name = Sym.make_with_string "idiv"
let imod_name = Sym.make_with_string "imod"
let ilt_name = Sym.make_with_string "ilt"
let ilte_name = Sym.make_with_string "ilte"
let igt_name = Sym.make_with_string "igt"
let igte_name = Sym.make_with_string "igte"
let ieq_name = Sym.make_with_string "ieq"
let ineq_name = Sym.make_with_string "ineq"
let ineg_name = Sym.make_with_string "ineg"

let uadd_name = Sym.make_with_string "uadd"
let usub_name = Sym.make_with_string "usub"
let umul_name = Sym.make_with_string "umul"
let udiv_name = Sym.make_with_string "udiv"
let umod_name = Sym.make_with_string "umod"
let ult_name = Sym.make_with_string "ult"
let ulte_name = Sym.make_with_string "ulte"
let ugt_name = Sym.make_with_string "ugt"
let ugte_name = Sym.make_with_string "ugte"
let ueq_name = Sym.make_with_string "ueq"
let uneq_name = Sym.make_with_string "uneq"
let uneg_name = Sym.make_with_string "uneg"

(* ****** ****** *)

let add_int0_int0_name = Sym.make_with_string "add_int0_int0"
let sub_int0_int0_name = Sym.make_with_string "sub_int0_int0"
let mul_int0_int0_name = Sym.make_with_string "mul_int0_int0"
let div_int0_int0_name = Sym.make_with_string "div_int0_int0"
let mod_int0_int0_name = Sym.make_with_string "mod_int0_int0"
let lt_int0_int0_name = Sym.make_with_string "lt_int0_int0"
let lte_int0_int0_name = Sym.make_with_string "lte_int0_int0"
let gt_int0_int0_name = Sym.make_with_string "gt_int0_int0"
let gte_int0_int0_name = Sym.make_with_string "gte_int0_int0"
let eq_int0_int0_name = Sym.make_with_string "eq_int0_int0"
let neq_int0_int0_name = Sym.make_with_string "neq_int0_int0"
let neg_int0_name = Sym.make_with_string "neg_int0"

let add_uint0_uint0_name = Sym.make_with_string "add_uint0_uint0"
let sub_uint0_uint0_name = Sym.make_with_string "sub_uint0_uint0"
let mul_uint0_uint0_name = Sym.make_with_string "mul_uint0_uint0"
let div_uint0_uint0_name = Sym.make_with_string "div_uint0_uint0"
let mod_uint0_uint0_name = Sym.make_with_string "mod_uint0_uint0"
let lt_uint0_uint0_name = Sym.make_with_string "lt_uint0_uint0"
let lte_uint0_uint0_name = Sym.make_with_string "lte_uint0_uint0"
let gt_uint0_uint0_name = Sym.make_with_string "gt_uint0_uint0"
let gte_uint0_uint0_name = Sym.make_with_string "gte_uint0_uint0"
let eq_uint0_uint0_name = Sym.make_with_string "eq_uint0_uint0"
let neq_uint0_uint0_name = Sym.make_with_string "neq_uint0_uint0"
let neg_uint0_name = Sym.make_with_string "neg_uint0"

(* ****** ****** *)

let add_int8_int8_name = Sym.make_with_string "add_int8_int8"
let sub_int8_int8_name = Sym.make_with_string "sub_int8_int8"
let mul_int8_int8_name = Sym.make_with_string "mul_int8_int8"
let div_int8_int8_name = Sym.make_with_string "div_int8_int8"
let mod_int8_int8_name = Sym.make_with_string "mod_int8_int8"
let lt_int8_int8_name = Sym.make_with_string "lt_int8_int8"
let lte_int8_int8_name = Sym.make_with_string "lte_int8_int8"
let gt_int8_int8_name = Sym.make_with_string "gt_int8_int8"
let gte_int8_int8_name = Sym.make_with_string "gte_int8_int8"
let eq_int8_int8_name = Sym.make_with_string "eq_int8_int8"
let neq_int8_int8_name = Sym.make_with_string "neq_int8_int8"
let neg_int8_name = Sym.make_with_string "neg_int8"

(* ****** ****** *)

let add_int16_int16_name = Sym.make_with_string "add_int16_int16"
let sub_int16_int16_name = Sym.make_with_string "sub_int16_int16"
let mul_int16_int16_name = Sym.make_with_string "mul_int16_int16"
let div_int16_int16_name = Sym.make_with_string "div_int16_int16"
let mod_int16_int16_name = Sym.make_with_string "mod_int16_int16"
let lt_int16_int16_name = Sym.make_with_string "lt_int16_int16"
let lte_int16_int16_name = Sym.make_with_string "lte_int16_int16"
let gt_int16_int16_name = Sym.make_with_string "gt_int16_int16"
let gte_int16_int16_name = Sym.make_with_string "gte_int16_int16"
let eq_int16_int16_name = Sym.make_with_string "eq_int16_int16"
let neq_int16_int16_name = Sym.make_with_string "neq_int16_int16"
let neg_int16_name = Sym.make_with_string "neg_int16"

(* ****** ****** *)

let add_int32_int32_name = Sym.make_with_string "add_int32_int32"
let sub_int32_int32_name = Sym.make_with_string "sub_int32_int32"
let mul_int32_int32_name = Sym.make_with_string "mul_int32_int32"
let div_int32_int32_name = Sym.make_with_string "div_int32_int32"
let mod_int32_int32_name = Sym.make_with_string "mod_int32_int32"
let lt_int32_int32_name = Sym.make_with_string "lt_int32_int32"
let lte_int32_int32_name = Sym.make_with_string "lte_int32_int32"
let gt_int32_int32_name = Sym.make_with_string "gt_int32_int32"
let gte_int32_int32_name = Sym.make_with_string "gte_int32_int32"
let eq_int32_int32_name = Sym.make_with_string "eq_int32_int32"
let neq_int32_int32_name = Sym.make_with_string "neq_int32_int32"
let neg_int32_name = Sym.make_with_string "neg_int32"

(* ****** ****** *)

let add_int64_int64_name = Sym.make_with_string "add_int64_int64"
let sub_int64_int64_name = Sym.make_with_string "sub_int64_int64"
let mul_int64_int64_name = Sym.make_with_string "mul_int64_int64"
let div_int64_int64_name = Sym.make_with_string "div_int64_int64"
let mod_int64_int64_name = Sym.make_with_string "mod_int64_int64"
let lt_int64_int64_name = Sym.make_with_string "lt_int64_int64"
let lte_int64_int64_name = Sym.make_with_string "lte_int64_int64"
let gt_int64_int64_name = Sym.make_with_string "gt_int64_int64"
let gte_int64_int64_name = Sym.make_with_string "gte_int64_int64"
let eq_int64_int64_name = Sym.make_with_string "eq_int64_int64"
let neq_int64_int64_name = Sym.make_with_string "neq_int64_int64"
let neg_int64_name = Sym.make_with_string "neg_int64"

(* ****** ****** *)

let add_lint_lint_name = Sym.make_with_string "add_lint_lint"
let sub_lint_lint_name = Sym.make_with_string "sub_lint_lint"
let mul_lint_lint_name = Sym.make_with_string "mul_lint_lint"
let div_lint_lint_name = Sym.make_with_string "div_lint_lint"
let mod_lint_lint_name = Sym.make_with_string "mod_lint_lint"
let lt_lint_lint_name = Sym.make_with_string "lt_lint_lint"
let lte_lint_lint_name = Sym.make_with_string "lte_lint_lint"
let gt_lint_lint_name = Sym.make_with_string "gt_lint_lint"
let gte_lint_lint_name = Sym.make_with_string "gte_lint_lint"
let eq_lint_lint_name = Sym.make_with_string "eq_lint_lint"
let neq_lint_lint_name = Sym.make_with_string "neq_lint_lint"
let neg_lint_name = Sym.make_with_string "neg_lint"

(* ****** ****** *)

let add_llint_llint_name = Sym.make_with_string "add_llint_llint"
let sub_llint_llint_name = Sym.make_with_string "sub_llint_llint"
let mul_llint_llint_name = Sym.make_with_string "mul_llint_llint"
let div_llint_llint_name = Sym.make_with_string "div_llint_llint"
let mod_llint_llint_name = Sym.make_with_string "mod_llint_llint"
let lt_llint_llint_name = Sym.make_with_string "lt_llint_llint"
let lte_llint_llint_name = Sym.make_with_string "lte_llint_llint"
let gt_llint_llint_name = Sym.make_with_string "gt_llint_llint"
let gte_llint_llint_name = Sym.make_with_string "gte_llint_llint"
let eq_llint_llint_name = Sym.make_with_string "eq_llint_llint"
let neq_llint_llint_name = Sym.make_with_string "neq_llint_llint"
let neg_llint_name = Sym.make_with_string "neg_llint"

(* ****** ****** *)

let padd_name = Sym.make_with_string "padd"
let psub_name = Sym.make_with_string "psub"
let plt_name = Sym.make_with_string "plt"
let plte_name = Sym.make_with_string "plte"
let pgt_name = Sym.make_with_string "pgt"
let pgte_name = Sym.make_with_string "pgte"
let peq_name = Sym.make_with_string "peq"
let pneq_name = Sym.make_with_string "pneq"

(* ****** ****** *)

let dcst2_is_add (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name iadd_name ||
    Sym.eq name uadd_name ||
    Sym.eq name padd_name ||
    Sym.eq name add_int0_int0_name ||
    Sym.eq name add_uint0_uint0_name ||
    Sym.eq name add_int8_int8_name ||
    Sym.eq name add_int16_int16_name ||
    Sym.eq name add_int32_int32_name ||
    Sym.eq name add_int64_int64_name ||
    Sym.eq name add_lint_lint_name ||
    Sym.eq name add_llint_llint_name ||
    Sym.eq name add_bool0_bool0_name ||
    Sym.eq name add_bool1_bool1_name ||
    Sym.eq name add_double_double_name ||
    Sym.eq name add_float_float_name ||
    false
(* end of [dcst2_is_add] *)

let dcst2_is_sub (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name isub_name ||
    Sym.eq name usub_name ||
    Sym.eq name psub_name ||
    Sym.eq name sub_int0_int0_name ||
    Sym.eq name sub_int8_int8_name ||
    Sym.eq name sub_int16_int16_name ||
    Sym.eq name sub_int32_int32_name ||
    Sym.eq name sub_int64_int64_name ||
    Sym.eq name sub_lint_lint_name ||
    Sym.eq name sub_llint_llint_name ||
    Sym.eq name sub_bool0_bool0_name ||
    Sym.eq name sub_bool1_bool1_name ||
    Sym.eq name sub_double_double_name ||
    Sym.eq name sub_float_float_name ||
    false
(* end of [dcst2_is_sub] *)

let dcst2_is_mul (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name imul_name ||
    Sym.eq name nmul_name ||
    Sym.eq name umul_name ||
    Sym.eq name mul_int0_int0_name ||
    Sym.eq name mul_uint0_uint0_name ||
    Sym.eq name mul_int8_int8_name ||
    Sym.eq name mul_int16_int16_name ||
    Sym.eq name mul_int32_int32_name ||
    Sym.eq name mul_int64_int64_name ||
    Sym.eq name mul_lint_lint_name ||
    Sym.eq name mul_llint_llint_name ||
    Sym.eq name mul_bool0_bool0_name ||
    Sym.eq name mul_bool1_bool1_name ||
    Sym.eq name mul_double_double_name ||
    Sym.eq name mul_float_float_name ||
    false
(* end of [dcst2_is_mul] *)

let dcst2_is_div (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name idiv_name ||
    Sym.eq name udiv_name ||
    Sym.eq name div_int0_int0_name ||
    Sym.eq name div_uint0_uint0_name ||
    Sym.eq name div_int8_int8_name ||
    Sym.eq name div_int16_int16_name ||
    Sym.eq name div_int32_int32_name ||
    Sym.eq name div_int64_int64_name ||
    Sym.eq name div_lint_lint_name ||
    Sym.eq name div_llint_llint_name ||
    Sym.eq name div_double_double_name ||
    Sym.eq name div_float_float_name ||
    false
(* end of [dcst2_is_div] *)


let dcst2_is_mod (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name imod_name ||
    Sym.eq name umod_name ||
    Sym.eq name mod_int0_int0_name ||
    Sym.eq name mod_uint0_uint0_name ||
    Sym.eq name mod_int8_int8_name ||
    Sym.eq name mod_int16_int16_name ||
    Sym.eq name mod_int32_int32_name ||
    Sym.eq name mod_int64_int64_name ||
    Sym.eq name mod_lint_lint_name ||
    Sym.eq name mod_llint_llint_name ||
    Sym.eq name mod_double_double_name ||
    Sym.eq name mod_float_float_name ||
    false
(* end of [dcst2_is_mod] *)

(* ****** ****** *)

let dcst2_is_lt (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name ilt_name ||
    Sym.eq name ult_name ||
    Sym.eq name plt_name ||
    Sym.eq name lt_int0_int0_name ||
    Sym.eq name lt_uint0_uint0_name ||
    Sym.eq name lt_int8_int8_name ||
    Sym.eq name lt_int16_int16_name ||
    Sym.eq name lt_int32_int32_name ||
    Sym.eq name lt_int64_int64_name ||
    Sym.eq name lt_lint_lint_name ||
    Sym.eq name lt_llint_llint_name ||
    Sym.eq name lt_char0_char0_name ||
    Sym.eq name lt_char1_char1_name ||
    Sym.eq name lt_double_double_name ||
    Sym.eq name lt_float_float_name ||
    false
(* end of [dcst2_is_lt] *)

let dcst2_is_lte (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name ilte_name ||
    Sym.eq name ulte_name ||
    Sym.eq name plte_name ||
    Sym.eq name lte_int0_int0_name ||
    Sym.eq name lte_uint0_uint0_name ||
    Sym.eq name lte_int8_int8_name ||
    Sym.eq name lte_int16_int16_name ||
    Sym.eq name lte_int32_int32_name ||
    Sym.eq name lte_int64_int64_name ||
    Sym.eq name lte_lint_lint_name ||
    Sym.eq name lte_llint_llint_name ||
    Sym.eq name lte_char0_char0_name ||
    Sym.eq name lte_char1_char1_name ||
    Sym.eq name lte_double_double_name ||
    Sym.eq name lte_float_float_name ||
    false
(* end of [dcst2_is_lte] *)

let dcst2_is_gt (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name igt_name ||
    Sym.eq name ugt_name ||
    Sym.eq name pgt_name ||
    Sym.eq name gt_int0_int0_name ||
    Sym.eq name gt_uint0_uint0_name ||
    Sym.eq name gt_int8_int8_name ||
    Sym.eq name gt_int16_int16_name ||
    Sym.eq name gt_int32_int32_name ||
    Sym.eq name gt_int64_int64_name ||
    Sym.eq name gt_lint_lint_name ||
    Sym.eq name gt_llint_llint_name ||
    Sym.eq name gt_char0_char0_name ||
    Sym.eq name gt_char1_char1_name ||
    Sym.eq name gt_double_double_name ||
    Sym.eq name gt_float_float_name ||
    false
(* end of [dcst2_is_gt] *)

let dcst2_is_gte (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name igte_name ||
    Sym.eq name ugte_name ||
    Sym.eq name pgte_name ||
    Sym.eq name gte_int0_int0_name ||
    Sym.eq name gte_uint0_uint0_name ||
    Sym.eq name gte_int8_int8_name ||
    Sym.eq name gte_int16_int16_name ||
    Sym.eq name gte_int32_int32_name ||
    Sym.eq name gte_int64_int64_name ||
    Sym.eq name gte_lint_lint_name ||
    Sym.eq name gte_llint_llint_name ||
    Sym.eq name gte_char0_char0_name ||
    Sym.eq name gte_char1_char1_name ||
    Sym.eq name gte_double_double_name ||
    Sym.eq name gte_float_float_name ||
    false
(* end of [dcst2_is_gte] *)

let dcst2_is_eq (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name ieq_name ||
    Sym.eq name ueq_name ||
    Sym.eq name peq_name ||
    Sym.eq name eq_int0_int0_name ||
    Sym.eq name eq_int8_int8_name ||
    Sym.eq name eq_int16_int16_name ||
    Sym.eq name eq_int32_int32_name ||
    Sym.eq name eq_int64_int64_name ||
    Sym.eq name eq_lint_lint_name ||
    Sym.eq name eq_llint_llint_name ||
    Sym.eq name eq_bool0_bool0_name ||
    Sym.eq name eq_bool1_bool1_name ||
    Sym.eq name eq_char0_char0_name ||
    Sym.eq name eq_char1_char1_name ||
    Sym.eq name eq_double_double_name ||
    Sym.eq name eq_float_float_name ||
    false
(* end of [dcst2_is_eq] *)

let dcst2_is_neq (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name ineq_name ||
    Sym.eq name uneq_name ||
    Sym.eq name pneq_name ||
    Sym.eq name neq_int0_int0_name ||
    Sym.eq name neq_uint0_uint0_name ||
    Sym.eq name neq_int8_int8_name ||
    Sym.eq name neq_int16_int16_name ||
    Sym.eq name neq_int32_int32_name ||
    Sym.eq name neq_int64_int64_name ||
    Sym.eq name neq_lint_lint_name ||
    Sym.eq name neq_llint_llint_name ||
    Sym.eq name neq_bool0_bool0_name ||
    Sym.eq name neq_bool1_bool1_name ||
    Sym.eq name neq_char0_char0_name ||
    Sym.eq name neq_char1_char1_name ||
    Sym.eq name neq_double_double_name ||
    Sym.eq name neq_float_float_name ||
    false
(* end of [dcst2_is_neq] *)

let dcst2_is_neg (d2c: dcst2): bool =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name ineg_name ||
    Sym.eq name neg_int0_name ||
    Sym.eq name neg_int8_name ||
    Sym.eq name neg_int16_name ||
    Sym.eq name neg_int32_name ||
    Sym.eq name neg_int64_name ||
    Sym.eq name neg_lint_name ||
    Sym.eq name neg_llint_name ||
    Sym.eq name neg_bool0_name ||
    Sym.eq name neg_bool1_name ||
    Sym.eq name neg_float_name ||
    Sym.eq name neg_double_name ||
    false
(* end of [dcst2_is_neg] *)

(* ****** ****** *)

let int1_of_int0_name = Sym.make_with_string "int1_of_int0"
let lint_of_int0_name = Sym.make_with_string "lint_of_int0"
let llint_of_int0_name = Sym.make_with_string "llint_of_int0"
let double_of_int0_name = Sym.make_with_string "double_of_int0"
let float_of_int0_name = Sym.make_with_string "float_of_int0"

let dcst2_is_of_int0 (d2c: dcst2) =
  let name = Syn.sym_of_did (d2c.dcst2_name) in
    Sym.eq name int1_of_int0_name ||
    Sym.eq name lint_of_int0_name ||
    Sym.eq name llint_of_int0_name ||
    Sym.eq name double_of_int0_name ||
    Sym.eq name float_of_int0_name ||
    false
(* end of [dcst2_is_of_int0] *)

(* ****** ****** *)

(* end of [ats_dyncst2.ml] *)
