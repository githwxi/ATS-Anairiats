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
// Time: February 2008

(* ****** ****** *)

(* for representing and handling constraints *)

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_trans3_env.sats"

(* ****** ****** *)

datatype s3aexp = (* static address expression *)
  | S3AEcst of (* abstract constant *)
      s2cst_t
  | S3AEexp of
      s2exp
  | S3AEvar of
      s2var_t
  | S3AEnull (* the null address *)
  | S3AEpadd of (* pointer arithmetic *)
      (s3aexp, s3iexp)
// end of [s3aexp]

and s3bexp = (* static boolean expression *)
  | S3BEcst of s2cst_t (* abstract constant *)
  | S3BEexp of s2exp
  | S3BEvar of s2var_t
  | S3BEbool of bool (* boolean constant *)
  | S3BEbadd of (s3bexp, s3bexp)
  | S3BEbmul of (s3bexp, s3bexp)
  | S3BEbneg of s3bexp
  // gte/lt : 2/~2; eq/neq: 1/~1
  | S3BEiexp of (int(*knd*), s3iexp)
// end of [s3bexp]

and s3iexp = (* static integer expression *)
  | S3IEcst of s2cst_t (* abstract constant *)
  | S3IEexp of s2exp
  | S3IEint of int
  | S3IEintinf of intinf_t
  | S3IEvar of s2var_t
  | S3IEineg of s3iexp
  | S3IEiadd of (s3iexp, s3iexp)
  | S3IEisub of (s3iexp, s3iexp)
  | S3IEimul of (s3iexp, s3iexp)
  | S3IEpdiff of (s3aexp, s3aexp)
// end of [s3iexp]

viewtypedef s3aexpopt_vt = Option_vt s3aexp

typedef s3bexplst = List s3bexp
typedef s3bexpopt = Option s3bexp
viewtypedef s3bexpopt_vt = Option_vt s3bexp

viewtypedef s3iexpopt_vt = Option_vt s3iexp

(* ****** ****** *)

fun fprint_s3aexp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s3ae: s3aexp): void
overload fprint with fprint_s3aexp

fun fprint_s3bexp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s3be: s3bexp): void
overload fprint with fprint_s3bexp

fun fprint_s3bexplst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s3bes: s3bexplst): void
overload fprint with fprint_s3bexplst

fun fprint_s3iexp {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s3ie: s3iexp): void
overload fprint with fprint_s3iexp

(* ****** ****** *)

fun print_s3aexp (_: s3aexp): void
fun print_s3bexp (_: s3bexp): void
fun print_s3bexplst (_: s3bexplst): void
fun print_s3iexp (_: s3iexp): void

overload print with print_s3aexp
overload print with print_s3bexp
overload print with print_s3bexplst
overload print with print_s3iexp

fun prerr_s3aexp (_: s3aexp): void
fun prerr_s3bexp (_: s3bexp): void
fun prerr_s3bexplst (_: s3bexplst): void
fun prerr_s3iexp (_: s3iexp): void

overload prerr with prerr_s3aexp
overload prerr with prerr_s3bexp
overload prerr with prerr_s3bexplst
overload prerr with prerr_s3iexp

(* ****** ****** *)

val s3aexp_null : s3aexp

fun s3aexp_cst (s2c: s2cst_t): s3aexp
fun s3aexp_var (s2v: s2var_t): s3aexp

fun s3aexp_padd (s3ae1: s3aexp, s3ie2: s3iexp): s3aexp
fun s3aexp_psub (s3ae1: s3aexp, s3ie2: s3iexp): s3aexp

fun s3aexp_psucc (s3ae: s3aexp): s3aexp
fun s3aexp_ppred (s3ae: s3aexp): s3aexp

(* ****** ****** *)

val s3bexp_true: s3bexp
val s3bexp_false: s3bexp

fun s3bexp_cst (s2c: s2cst_t): s3bexp
fun s3bexp_var (s2v: s2var_t): s3bexp

fun s3bexp_bneg (s3be: s3bexp): s3bexp

fun s3bexp_beq (s3be1: s3bexp, s3be2: s3bexp): s3bexp
fun s3bexp_bneq (s3be1: s3bexp, s3be2: s3bexp): s3bexp

fun s3bexp_badd (s3be1: s3bexp, s3be2: s3bexp): s3bexp
fun s3bexp_bmul (s3be1: s3bexp, s3be2: s3bexp): s3bexp

fun s3bexp_iexp (knd: int, s3ie: s3iexp): s3bexp

fun s3bexp_igt (s3ie1: s3iexp, s3ie2: s3iexp): s3bexp
fun s3bexp_igte (s3ie1: s3iexp, s3ie2: s3iexp): s3bexp
fun s3bexp_ilt (s3ie1: s3iexp, s3ie2: s3iexp): s3bexp
fun s3bexp_ilte (s3ie1: s3iexp, s3ie2: s3iexp): s3bexp

fun s3bexp_ieq (s3ie1: s3iexp, s3ie2: s3iexp): s3bexp
fun s3bexp_ineq (s3ie1: s3iexp, s3ie2: s3iexp): s3bexp

fun s3bexp_pgt (s3ae1: s3aexp, s3ae2: s3aexp): s3bexp
fun s3bexp_pgte (s3ae1: s3aexp, s3ae2: s3aexp): s3bexp
fun s3bexp_plt (s3ae1: s3aexp, s3ae2: s3aexp): s3bexp
fun s3bexp_plte (s3ae1: s3aexp, s3ae2: s3aexp): s3bexp

fun s3bexp_peq (s3ae1: s3aexp, s3ae2: s3aexp): s3bexp
fun s3bexp_pneq (s3ae1: s3aexp, s3ae2: s3aexp): s3bexp

(* ****** ****** *)

val s3iexp_0 : s3iexp
val s3iexp_1 : s3iexp
val s3iexp_neg_1 : s3iexp

fun s3iexp_cst (s2c: s2cst_t): s3iexp
fun s3iexp_int (i: int): s3iexp
fun s3iexp_intinf (i: intinf_t): s3iexp
fun s3iexp_var (s2v: s2var_t): s3iexp

fun s3iexp_ineg (s3ie: s3iexp): s3iexp
fun s3iexp_iadd (s3ie1: s3iexp, s3ie2: s3iexp): s3iexp
fun s3iexp_isub (s3ie1: s3iexp, s3ie2: s3iexp): s3iexp
fun s3iexp_imul (s3ie1: s3iexp, s3ie2: s3iexp): s3iexp

fun s3iexp_isucc (s3ie: s3iexp): s3iexp
fun s3iexp_ipred (s3ie: s3iexp): s3iexp

fun s3iexp_pdiff (s3ae1: s3aexp, s3ae2: s3aexp): s3iexp

(* ****** ****** *)

dataviewtype s2cfdeflst_vt =
  | S2CFDEFLSTcons of (
      s2cst_t(*scf*), s2explst(*arg*), s2var_t(*res*), s3bexpopt_vt(*rel*), s2cfdeflst_vt
    ) // end of [S2CFDEFLSTcons]
  | S2CFDEFLSTmark of s2cfdeflst_vt
  | S2CFDEFLSTnil
// end of [s2cfdeflst_vt]

fun s3aexp_make_s2exp
  (s2e: s2exp, s2cs: &s2cstlst, fds: &s2cfdeflst_vt): s3aexpopt_vt
// end of [s3aexp_make_s2exp]

fun s3bexp_make_s2exp
  (s2e: s2exp, s2cs: &s2cstlst, fds: &s2cfdeflst_vt): s3bexpopt_vt
fun s3bexp_make_h3ypo
  (h3p: h3ypo, s2cs: &s2cstlst, fds: &s2cfdeflst_vt): s3bexpopt_vt

fun s3iexp_make_s2exp
  (s2e: s2exp, s2cs: &s2cstlst, fds: &s2cfdeflst_vt): s3iexpopt_vt
// end of [s3iexp_make_s2exp]

(* ****** ****** *)

fun c3str_solve (c3t: c3str): void

(* ****** ****** *)

(* end of [ats_constraint.sats] *)
