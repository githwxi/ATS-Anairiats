(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November 2007

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

abstype s2cstref_t // boxed type

fun s2cstref_make (name: string): s2cstref_t

fun s2cstref_get_cst (_: s2cstref_t): s2cst_t
fun s2cstref_get_exp (_: s2cstref_t, _: Option_vt s2explst): s2exp
fun s2cstref_unget_exp (_: s2cstref_t, _: s2exp): Option_vt (s2explst)
fun s2cstref_equ_cst (_: s2cstref_t, _: s2cst_t): bool
fun s2cstref_equ_exp (_: s2cstref_t, _: s2exp): bool

(* ****** ****** *)

val True_bool : s2cstref_t and False_bool : s2cstref_t

(* ****** ****** *)

val Bool_t0ype : s2cstref_t
val Bool_bool_t0ype : s2cstref_t
val Byte_t0ype : s2cstref_t
val Char_t0ype : s2cstref_t
val Char_char_t0ype : s2cstref_t
val Double_t0ype : s2cstref_t
val Double_long_t0ype : s2cstref_t
val Float_t0ype : s2cstref_t
val Int_t0ype : s2cstref_t
val Int_int_t0ype : s2cstref_t
val Lint_t0ype : s2cstref_t
val Lint_int_t0ype : s2cstref_t
val Opt_viewt0ype_bool_viewt0ype : s2cstref_t
val Ptr_type : s2cstref_t
val Ptr_addr_type : s2cstref_t
val Ref_viewt0ype_type : s2cstref_t
val Size_t0ype : s2cstref_t
val Size_int_t0ype : s2cstref_t
val Ssize_t0ype : s2cstref_t
val Ssize_int_t0ype : s2cstref_t
val Strbuf_t0ype : s2cstref_t
val Strbuf_int_int_t0ype : s2cstref_t
val String_type : s2cstref_t
val String_int_type : s2cstref_t
val Uint_t0ype : s2cstref_t
val Uint_int_t0ype : s2cstref_t
val Ulint_t0ype : s2cstref_t
val Ulint_int_t0ype : s2cstref_t
val Void_t0ype : s2cstref_t

(* ****** ****** *)

val Int_long_t0ype : s2cstref_t
val Int_long_long_t0ype : s2cstref_t

val Uint_long_t0ype : s2cstref_t
val Uint_long_long_t0ype : s2cstref_t

val Int_short_t0ype : s2cstref_t
val Int_short_short_t0ype : s2cstref_t

val Uint_short_t0ype : s2cstref_t
val Uint_short_short_t0ype : s2cstref_t

(* ****** ****** *)

val Bottom_t0ype_exi : s2cstref_t
val Bottom_t0ype_uni : s2cstref_t

val Bottom_viewt0ype_exi : s2cstref_t
val Bottom_viewt0ype_uni : s2cstref_t

val Exception_viewtype : s2cstref_t
val None_viewt0ype : s2cstref_t

(* ****** ****** *)

val Array_viewt0ype_int_type : s2cstref_t
val Array_viewt0ype_int_viewtype : s2cstref_t
val Arrayptrsize_viewt0ype_int_viewt0ype : s2cstref_t

(* ****** ****** *)

val List_t0ype_int_type : s2cstref_t
val List_viewt0ype_int_viewtype : s2cstref_t

(* ****** ****** *)

val At_viewt0ype_addr_view : s2cstref_t

(* ****** ****** *)

val Crypt_viewt0ype_viewt0ype : s2cstref_t

(* ****** ****** *)

val Clo_viewt0ype_viewt0ype : s2cstref_t
val Cloptr_viewt0ype_viewtype : s2cstref_t
val Cloref_t0ype_type : s2cstref_t

(* ****** ****** *)

val Lazy_t0ype_type : s2cstref_t
val Lazy_viewt0ype_viewtype : s2cstref_t

(* ****** ****** *)

val Printf_c_types_type : s2cstref_t
val Va_list_viewt0ype : s2cstref_t // variadicity
val Va_list_types_viewt0ype : s2cstref_t // variadicity

(* ****** ****** *)

val Vbox_view_prop : s2cstref_t

(* ****** ****** *)

val Neg_bool_bool : s2cstref_t
val Add_bool_bool_bool : s2cstref_t 
val Mul_bool_bool_bool : s2cstref_t 

val Eq_bool_bool_bool : s2cstref_t 
val Neq_bool_bool_bool : s2cstref_t 

(* ****** ****** *)

val Sub_char_char_int : s2cstref_t

val Gt_char_char_bool : s2cstref_t
val Gte_char_char_bool : s2cstref_t
val Lt_char_char_bool : s2cstref_t
val Lte_char_char_bool : s2cstref_t

val Eq_char_char_bool : s2cstref_t
val Neq_char_char_bool : s2cstref_t

(* ****** ****** *)

val Neg_int_int : s2cstref_t
val Add_int_int_int : s2cstref_t
val Sub_int_int_int : s2cstref_t
val Mul_int_int_int : s2cstref_t

val Gt_int_int_bool : s2cstref_t
val Gte_int_int_bool : s2cstref_t
val Lt_int_int_bool : s2cstref_t
val Lte_int_int_bool : s2cstref_t

val Eq_int_int_bool : s2cstref_t
val Neq_int_int_bool : s2cstref_t

//

val Div_int_int_int : s2cstref_t
val Div_int_int_int_bool : s2cstref_t

val Max_int_int_int : s2cstref_t
val Max_int_int_int_bool : s2cstref_t

val Min_int_int_int : s2cstref_t
val Min_int_int_int_bool : s2cstref_t

val Abs_int_int : s2cstref_t
val Abs_int_int_bool : s2cstref_t

val Btw_int_int_int_bool : s2cstref_t

val IntOfBool_bool_int : s2cstref_t
val IntOfBool_bool_int_bool : s2cstref_t

val Size_int_int_bool : s2cstref_t
val Sizeof_viewt0ype_int : s2cstref_t

(* ****** ****** *)

val Null_addr: s2cstref_t

val Add_addr_int_addr : s2cstref_t
val Sub_addr_int_addr : s2cstref_t
val Sub_addr_addr_int : s2cstref_t

val Gt_addr_addr_bool : s2cstref_t
val Gte_addr_addr_bool : s2cstref_t
val Lt_addr_addr_bool : s2cstref_t
val Lte_addr_addr_bool : s2cstref_t

val Eq_addr_addr_bool : s2cstref_t
val Neq_addr_addr_bool : s2cstref_t

(* ****** ****** *)

val Lte_cls_cls_bool : s2cstref_t

(* ****** ****** *)

abstype d2conref_t // boxed type

fun d2conref_make (name: string): d2conref_t
fun d2conref_con_get (_: d2conref_t): d2con_t

val List_nil : d2conref_t and List_cons : d2conref_t
val List_vt_nil : d2conref_t and List_vt_cons : d2conref_t

(*

// it is now supported internally; see [prelude/CATS/lazy.cats]

val ThunkValue_thunk : d2conref_t and ThunkValue_value : d2conref_t
val ThunkValue_vt_thunk : d2conref_t and ThunkValue_vt_value : d2conref_t

*)

(* ****** ****** *)

abstype d2cstref_t // boxed type

fun d2cstref_make (name: string): d2cstref_t
fun d2cstref_get_cst (_: d2cstref_t): d2cst_t

val Ats_main_void : d2cstref_t
val Ats_main_argc_argv : d2cstref_t
val Ats_main_dummy : d2cstref_t

(* ****** ****** *)

fun s2exp_bool (b: bool): s2exp
fun s2exp_bool_t0ype (): s2exp
fun s2exp_bool_bool_t0ype (b: bool): s2exp
fun s2exp_char_t0ype (): s2exp
fun s2exp_char_char_t0ype (c: char): s2exp
fun s2exp_double_t0ype (): s2exp
fun s2exp_double_long_t0ype (): s2exp
fun s2exp_float_t0ype (): s2exp
fun s2exp_int_t0ype (): s2exp
fun s2exp_int_int_t0ype (i: int): s2exp
fun s2exp_int_intinf_t0ype (i: intinf_t): s2exp

fun s2exp_ptr_type (): s2exp
fun s2exp_ptr_addr_type (addr: s2exp): s2exp
fun s2exp_ref_viewt0ype_type (elt: s2exp): s2exp
fun s2exp_string_type (): s2exp
fun s2exp_string_int_type (n: int): s2exp
fun s2exp_void_t0ype (): s2exp
fun s2exp_uint_t0ype (): s2exp
fun s2exp_uint_int_t0ype (i: int): s2exp
fun s2exp_uint_intinf_t0ype (i: intinf_t): s2exp

(* ****** ****** *)

fun un_s2exp_bool_bool_t0ype (s2e: s2exp): Option_vt (s2exp)
fun un_s2exp_char_char_t0ype (s2e: s2exp): Option_vt (s2exp)
fun un_s2exp_int_int_t0ype (s2e: s2exp): Option_vt (s2exp)
fun un_s2exp_ptr_addr_type (s2e: s2exp): Option_vt (s2exp(*addr*))
fun un_s2exp_ref_viewt0ype_type (s2e: s2exp): Option_vt (s2exp(*elt*))
fun un_s2exp_size_int_t0ype (s2e: s2exp): Option_vt (s2exp)
fun un_s2exp_string_int_type (s2e: s2exp): Option_vt (s2exp)

(* ****** ****** *)

fun s2exp_lint_t0ype (): s2exp
fun s2exp_lint_intinf_t0ype (i: intinf_t): s2exp

fun s2exp_ulint_t0ype (): s2exp
fun s2exp_ulint_intinf_t0ype (i: intinf_t): s2exp

fun s2exp_llint_t0ype (): s2exp
fun s2exp_ullint_t0ype (): s2exp

fun s2exp_sint_t0ype (): s2exp
fun s2exp_usint_t0ype (): s2exp

fun s2exp_ssint_t0ype (): s2exp
fun s2exp_ussint_t0ype (): s2exp

(* ****** ****** *)

fun s2exp_bottom_t0ype_exi (): s2exp
fun s2exp_bottom_t0ype_uni (): s2exp

fun s2exp_bottom_viewt0ype_exi (): s2exp
fun s2exp_bottom_viewt0ype_uni (): s2exp

fun s2exp_exception_viewtype (): s2exp

(* ****** ****** *)

fun s2exp_at_viewt0ype_addr_view (elt: s2exp, addr: s2exp): s2exp

fun un_s2exp_at_viewt0ype_addr_view
  (s2e: s2exp) : Option_vt @(s2exp(*elt*), s2exp(*addr*))

(* ****** ****** *)

fun s2exp_array_viewt0ype_int_type (elt: s2exp, sz: int): s2exp
fun s2exp_array_viewt0ype_int_viewtype (elt: s2exp, sz: int): s2exp
fun s2exp_arrayptrsize_viewt0ype_int_viewt0ype (elt: s2exp, sz: int): s2exp

(* ****** ****** *)

fun s2exp_list_t0ype_int_type (elt: s2exp, ln: int): s2exp
fun s2exp_list_viewt0ype_int_viewtype (elt: s2exp, ln: int): s2exp

fun un_s2exp_list_t0ype_int_type
  (s2e: s2exp): Option_vt @(s2exp(*elt*), s2exp(*size*))

(* ****** ****** *)

fun clo_viewt0ype_viewt0ype_assume (): void
fun cloptr_viewt0ype_viewtype_assume (): void
fun cloref_t0ype_type_assume (): void

(* ****** ****** *)

fun crypt_viewt0ype_viewt0ype_assume (): void

(* ****** ****** *)

fun s2exp_lazy_t0ype_type (_: s2exp): s2exp
fun s2exp_lazy_viewt0ype_viewtype (_: s2exp): s2exp

fun un_s2exp_lazy_t0ype_type (_: s2exp): Option_vt (s2exp(*elt*))
fun un_s2exp_lazy_viewt0ype_viewtype (_: s2exp): Option_vt (s2exp(*elt*))

(* ****** ****** *)

fun s2exp_printf_c_types_type (_: s2exp): s2exp

fun s2exp_va_list_viewt0ype (): s2exp
fun s2exp_va_list_types_viewt0ype (_: s2exp): s2exp

(* ****** ****** *)

fun s2exp_vbox_view_prop (_: s2exp): s2exp
fun un_s2exp_vbox_view_prop (s2e: s2exp) : Option_vt s2exp

(* ****** ****** *)

fun s2exp_neg_bool_bool (s2p: s2exp): s2exp
fun s2exp_add_bool_bool_bool (s2p1: s2exp, s2p2: s2exp): s2exp
fun s2exp_mul_bool_bool_bool (s2p1: s2exp, s2p2: s2exp): s2exp

(* ****** ****** *)

fun s2exp_gt_int_int_bool (s2e1: s2exp, s2e2: s2exp): s2exp
fun s2exp_gte_int_int_bool (s2e1: s2exp, s2e2: s2exp): s2exp

fun s2exp_lt_int_int_bool (s2e1: s2exp, s2e2: s2exp): s2exp
fun s2exp_lte_int_int_bool (s2e1: s2exp, s2e2: s2exp): s2exp

fun s2exp_eq_int_int_bool (s2e1: s2exp, s2e2: s2exp): s2exp
fun s2exp_neq_int_int_bool (s2e1: s2exp, s2e2: s2exp): s2exp

fun s2exp_btw_int_int_int_bool
  (lft: s2exp, mid: s2exp, rgt: s2exp): s2exp
// end of [s2exp_btw_int_int_int_bool]

(* ****** ****** *)

fun sizeof_viewt0ype_int_assume (): void

(* ****** ****** *)

fun s2exp_null_addr (): s2exp

fun s2exp_gt_addr_addr_bool (s2e1: s2exp, s2e2: s2exp): s2exp
fun s2exp_gte_addr_addr_bool (s2e1: s2exp, s2e2: s2exp): s2exp

fun s2exp_lt_addr_addr_bool (s2e1: s2exp, s2e2: s2exp): s2exp
fun s2exp_lte_addr_addr_bool (s2e1: s2exp, s2e2: s2exp): s2exp

(* ****** ****** *)

(* end of [ats_stadyncst2.sats] *)
