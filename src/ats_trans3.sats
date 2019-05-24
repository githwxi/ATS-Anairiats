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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December 2007
//
(* ****** ****** *)

staload
Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Syn = "ats_syntax.sats"
typedef funclo = $Syn.funclo

(* ****** ****** *)
//
staload SEXP2 = "ats_staexp2.sats"
typedef s2exp = $SEXP2.s2exp
typedef s2explst (n:int) = $SEXP2.s2explst (n)
typedef s2explst = $SEXP2.s2explst
typedef s2explstlst = $SEXP2.s2explstlst
typedef s2eff = $SEXP2.s2eff
typedef s2lab = $SEXP2.s2lab
typedef s2lablst = $SEXP2.s2lablst
//
staload DEXP2 = "ats_dynexp2.sats"
typedef d2cst_t = $DEXP2.d2cst_t
typedef d2var_t = $DEXP2.d2var_t
typedef p2at = $DEXP2.p2at
typedef p2atlst (n:int) = $DEXP2.p2atlst (n)
typedef p2atlst = $DEXP2.p2atlst
typedef d2exp = $DEXP2.d2exp
typedef d2explst (n:int) = $DEXP2.d2explst (n)
typedef d2explst = $DEXP2.d2explst
typedef d2expopt = $DEXP2.d2expopt
typedef d2explstlst = $DEXP2.d2explstlst
//
staload PATCST2 = "ats_patcst2.sats"
//
staload SOL = "ats_staexp2_solve.sats"
//
staload TRENV3 = "ats_trans3_env.sats"
//
(* ****** ****** *)

staload "ats_dynexp3.sats"

(* ****** ****** *)

fun d2exp_funclo_of_d2exp
  (d2e0: d2exp, fc0: &funclo): d2exp
// end of [d2exp_funclo_of_d2exp]

fun d2exp_s2eff_of_d2exp
  (d2e0: d2exp, s2fe0: &(s2eff?) >> s2eff) : d2exp
// end of [d2exp_s2eff_of_d2exp]

(* ****** ****** *)

fun d2exp_seq_typ_syn (d2es: d2explst): s2exp
fun d2exp_cstsp_typ_syn (cst: $Syn.cstsp): s2exp

(* ****** ****** *)

fun fshowtype_d3exp (d3e: d3exp): void

(* ****** ****** *)

fun d3exp_open_and_add (d3e: d3exp): void
fun d3explst_open_and_add (d3es: d3explst): void

(* ****** ****** *)

fun d3explstlst_get_ind
  (d3ess: d3explstlst): s2explstlst
// end of [d3explstlst_get_ind]

(* ****** ****** *)

fun p2at_tr_dn (_: p2at, _: s2exp): p3at
fun p2atlst_tr_dn {n:nat}
  (_: p2atlst n, _: s2explst n): p3atlst n

fun p2at_arg_tr_up (_: p2at): p3at
fun p2at_arg_tr_dn (_: p2at, _: s2exp): p3at

fun p2atlst_arg_tr_up {n:nat}
  (npf: int, _: p2atlst n): p3atlst n
fun p2atlst_arg_tr_dn {n:nat}
  (npf: int, _: p2atlst n, _: s2explst n): p3atlst n

(* ****** ****** *)
//
// HX: implemented in [ats_trans3_assgn.dats]
//
fun s2exp_addr_assgn_slablst (
  loc0: loc_t, s2e0: s2exp, s2ls: s2lablst, _new: s2exp
) : s2lablst // end of [s2exp_addr_assgn_slablst]

fun d2var_mut_assgn_slablst (
  loc0: loc_t, d2v: d2var_t, s2ls: s2lablst, _new: s2exp
) : s2lablst // end of [d2var_mut_assgn_slablst]

fun d2var_lin_assgn_slablst {n:nat} (
  loc0: loc_t, d2v: d2var_t, s2ls: list (s2lab, n), _new: s2exp
) : list (s2lab, n) // end of [d2var_lin_assgn_slablst]

(* ****** ****** *)
//
// HX: implemented in [ats_trans3_deref.dats]
//
fun s2exp_addr_deref_slablst (
  loc0: loc_t, s2e0: s2exp, s2ls: s2lablst
) : (s2exp(*result*), s2lablst)

(* ****** ****** *)
//
// HX: implemented in [ats_trans3_view.dats]
//
fun s2exp_addr_viewat_try_slablst (
  loc0: loc_t, s2e0: s2exp, s2ls: s2lablst
) : s2lablst // end of [s2exp_addr_viewat_try_slablst]

fun s2exp_addr_viewat_get_slablst (
  loc0: loc_t, s2e0: s2exp, s2ls: s2lablst
) : (
  s2exp // result
, s2lablst // path
, d2var_t // viewroot
, s2lablst // viewpath
) // end of [s2exp_addr_viewat_get_slablst]

fun s2exp_addr_viewat_set_slablst (
  loc0: loc_t, s2e0: s2exp, s2ls: s2lablst, s2e_new_at: s2exp
) : s2lablst // end of [s2exp_addr_viewat_set_slablst]

(* ****** ****** *)

fun d3exp_lval_set_typ (
  loc0: loc_t, refval: int, d3e0: d3exp, s2e: s2exp, err: &int
) : void // end of [d3exp_lval_set_typ]

fun d3exp_lval_set_typ_arg
  (refval: int, d3e0: d3exp, s2e: s2exp): int (*freeknd*)
// end of [d3exp_lval_set_typ_arg]

fun d3exp_lval_set_typ_pat (d3e0: d3exp, p3t: p3at): void

(* ****** ****** *)

fun d3exp_tr_dn (d3e: d3exp, s2e: s2exp): void

(* ****** ****** *)

fun d2exp_tr_up (_: d2exp): d3exp
fun d2explst_tr_up {n:nat} (_: d2explst n): d3explst n
fun d2explstlst_tr_up (_: d2explstlst): d3explstlst

fun d2exp_cst_tr_up (_: loc_t, d2c: d2cst_t): d3exp
fun d2exp_var_tr_up (_: loc_t, d2v: d2var_t): d3exp

// 0/1: break/continue
fun d2exp_loopexn_tr_up (_: loc_t, i: int): d3exp

fun d2exp_loop_tr_up (
  _: loc_t
, _inv: $DEXP2.loopi2nv
, _init: d2expopt
, _test: d2exp
, _post: d2expopt
, _body: d2exp
) : d3exp // end of [d2exp_loop_tr_up]

(* ****** ****** *)

fun assert_bool_tr_dn
  (loc: loc_t, b: bool, s2e: s2exp): void
// end of [assert_bool_tr_dn]

fun d2exp_tr_dn (_: d2exp, _: s2exp): d3exp
fun d2exp_tr_dn_rest (_: d2exp, _: s2exp): d3exp

fun d2exp_if_tr_dn (
  loc0: loc_t
, res: $DEXP2.i2nvresstate
, d2e_cond: d2exp
, d2e_then: d2exp
, od2e_else: d2expopt
, s2e0: s2exp
) : d3exp // end of [d2exp_if_tr_dn]

fun d2exp_caseof_tr_dn
  {n:nat} (
  loc: loc_t
, casknd: int
, res: $DEXP2.i2nvresstate
, n: int n
, d2es: d2explst n
, c2ls: $DEXP2.c2laulst n
, s2e0: s2exp
) : d3exp // end of [d2exp_caseof_tr_dn]

fun d2exp_sif_tr_dn (
  loc0: loc_t
, res: $DEXP2.i2nvresstate
, s2p_cond: s2exp
, d2e_then: d2exp
, d2e_else: d2exp
, s2e0: s2exp
) : d3exp // end of [d2exp_sif_tr_dn]

fun d2exp_scaseof_tr_dn (
  loc0: loc_t
, res: $DEXP2.i2nvresstate
, s2e_val: s2exp
, sc2ls: $DEXP2.sc2laulst
, s2e0: s2exp
) : d3exp // end of [d2exp_scaseof_tr_dn]

(* ****** ****** *)

dataviewtype
sacsbisopt =
  | {n:nat} SACSBISsome of ($TRENV3.staftscstr_t n, $TRENV3.stbefitemlst n)
  | SACSBISnone
// end of [sacsbisopt]

fun c2lau_tr_dn
  {n:nat} (
  c2l: $DEXP2.c2lau n
, op2tcss: Option_vt ($PATCST2.p2atcstlstlst n)
, d3es: d3explst n // for restoration
, n: int n
, s2es_pat: s2explst n
, s2e0_exp: s2exp
, osacsbis: sacsbisopt
) : c3lau n // end of [c2lau_tr_dn]

fun c2laulst_tr_dn
  {n:nat} (
  loc0: loc_t
, cmplt: &int
, casknd: int
, res: $DEXP2.i2nvresstate
, c2ls: $DEXP2.c2laulst n
, d3es: d3explst n
, n: int n
, s2es_pat: s2explst n
, s2e0: s2exp
) : c3laulst n // end of [c2laulst_tr_dn]

(* ****** ****** *)

fun d2ec_tr (_: $DEXP2.d2ec): d3ec
fun d2eclst_tr (_: $DEXP2.d2eclst): d3eclst
fun c3str_get_final (): $TRENV3.c3str

(* ****** ****** *)

(* end of [ats_trans3.sats] *)
