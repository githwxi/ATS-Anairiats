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

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

fun s1rt_tr (s1t: s1rt): s2rt
fun s1rtlst_tr (s1ts: s1rtlst): s2rtlst
fun s1rtopt_tr (os1t: s1rtopt): s2rtopt

fun effcst_tr (efc: $Eff.effcst): s2eff

fun d1atarglst_tr (d1as: d1atarglst): List @(symopt_t, s2rt, int)

fun s1arglst_var_tr (s1as: s1arglst): s2varlst
fun s1arglstlst_var_tr (s1ass: s1arglstlst): s2varlstlst

fun s1arg_var_tr_srt (s1a: s1arg, s2t: s2rt): s2var_t

fun sp1at_tr_dn (sp1t: sp1at, s2t_pat: s2rt): sp2at

(* ****** ****** *)

fun s1exp_tr_up (s1e: s1exp): s2exp
fun s1explst_tr_up (s1es: s1explst): s2explst
fun s1explstlst_tr_up (s1ess: s1explstlst): s2explstlst
fun tmps1explstlst_tr_up (ts1ess: tmps1explstlst): tmps2explstlst

//

fun s1exp_tr_dn (s1e: s1exp, s2t: s2rt): s2exp
fun s1explst_tr_dn {n:nat}
  (s1es: list (s1exp, n), s2ts: list (s2rt, n)): list (s2exp, n)
// end of [s1explst_tr_dn]

fun s1exp_tr_dn_bool (s1e: s1exp): s2exp
fun s1exp_tr_dn_cls (s1e: s1exp): s2exp
fun s1exp_tr_dn_int (s1e: s1exp): s2exp
fun s1exp_tr_dn_prop (s1e: s1exp): s2exp
fun s1exp_tr_dn_type (s1e: s1exp): s2exp
fun s1exp_tr_dn_t0ype (s1e: s1exp): s2exp
fun s1exp_tr_dn_view (s1e: s1exp): s2exp
fun s1exp_tr_dn_viewtype (s1e: s1exp): s2exp
fun s1exp_tr_dn_viewt0ype (s1e: s1exp): s2exp
fun s1exp_tr_dn_impredicative (s1e: s1exp): s2exp
fun s1expopt_tr_dn_impredicative (os1e: s1expopt): s2expopt

fun s1explst_tr_dn_bool (s1es: s1explst): s2explst
fun s1explst_tr_dn_cls (s1es: s1explst): s2explst
fun s1explst_tr_dn_int (s1es: s1explst): s2explst

// arg/res type translation
fun s1exp_arg_tr_up (s1e: s1exp, _: &wths1explst): s2exp
fun s1exp_arg_tr_dn_impredicative (s1e: s1exp, _: &wths1explst): s2exp
fun s1exp_res_tr_dn_impredicative (s1e: s1exp, _: wths1explst): s2exp

(* ****** ****** *)

fun s1qualst_tr (s1qs: s1qualst): @(s2varlst, s2explst)
fun s1qualstlst_tr (s1qss: s1qualstlst): s2qualst

(* ****** ****** *)

fun s1exparg_tr (s1a: s1exparg): s2exparg
fun s1exparglst_tr (s1as: s1exparglst): s2exparglst

(* ****** ****** *)

fun s1rtdeflst_tr (ds: s1rtdeflst): void

fun s1taconlst_tr (absknd: $Syn.abskind, ds: s1taconlst): void

fun s1tacstlst_tr (ds: s1tacstlst): void

fun s1tavarlst_tr (ds: s1tavarlst): s2tavarlst

fun d1atsrtdeclst_tr (ds: d1atsrtdeclst): void

fun s1expdef_tr (res: s2rtopt, d1c: s1expdef): s2cst_t
fun s1expdeflst_tr (res: s2rtopt, d1cs: s1expdeflst): void

fun s1aspdec_tr (d1c: s1aspdec): s2aspdec

fun d1cstdeclst_tr
  (dck: $Syn.dcstkind, decarg: s2qualst, d1cs: d1cstdeclst): d2cstlst
// end of [d1cstdeclst_tr]

fun d1atdeclst_tr
  (datknd: $Syn.datakind, d1cs_dat: d1atdeclst, d1cs_def: s1expdeflst)
  : s2cstlst
// end of [d1atdeclst_tr]

fun e1xndeclst_tr (d1cs: e1xndeclst): d2conlst

(* ****** ****** *)

fun p1at_tr (_: p1at): p2at
fun p1atlst_tr (_: p1atlst): p2atlst
fun labp1atlst_tr (_: labp1atlst): labp2atlst

fun p1at_arg_tr (_: p1at, _: &wths1explst): p2at
fun p1atlst_arg_tr (_: p1atlst, _: &wths1explst): p2atlst

(* ****** ****** *)
//
// HX: used in [ats_trans3_env]
//
fun p1at_con_instantiate (loc: loc_t, d2c: d2con_t): @(s2qualst, s2exp)
//
(* ****** ****** *)

fun d1exp_tr (_: d1exp): d2exp

fun d1explst_tr (_: d1explst): d2explst
fun d1expopt_tr (_: d1expopt): d2expopt

fun d1explstlst_tr (_: d1explstlst): d2explstlst

fun labd1explst_tr (_: labd1explst): labd2explst

fun d1lab_tr (_: d1lab): d2lab

(* ****** ****** *)

fun overload_def_tr
  (id: $Syn.i0de, d2i: d2item) : void
// end of [overload_def_tr]

fun overload_d2eclst_tr (d2cs: d2eclst): void

(* ****** ****** *)

fun d1ec_tr (d1c: d1ec): d2ec
fun d1eclst_tr (d1cs: d1eclst): d2eclst

(* ****** ****** *)

(* end of [ats_trans2.sats] *)
