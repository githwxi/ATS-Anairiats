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
// Time: December 2007

(* ****** ****** *)

staload Lab = "ats_label.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"

(* ****** ****** *)

fun label_equal_solve_err
  (_: loc_t, _: $Lab.label_t, _: $Lab.label_t, err: &int): void

fun stamp_equal_solve_err
  (_: loc_t, s1: stamp_t, s2: stamp_t, err: &int): void

fun funclo_equal_solve
  (_: loc_t, _: $Syn.funclo, _: $Syn.funclo): void
fun funclo_equal_solve_err
  (_: loc_t, _: $Syn.funclo, _: $Syn.funclo, err: &int): void

fun clokind_equal_solve_err
  (_: loc_t, knd1: int, knd2: int, err: &int): void

fun linearity_equal_solve_err
  (_: loc_t, lin1: int, lin2: int, err: &int): void

fun pfarity_equal_solve
  (_: loc_t, npf1: int, npf2: int): void
fun pfarity_equal_solve_err
  (_: loc_t, npf1: int, npf2: int, err: &int): void

fun tyreckind_equal_solve_err
  (_: loc_t, _: tyreckind, _: tyreckind, err: &int): void

fun refval_equal_solve_err
  (_: loc_t, refval1: int, refval2: int, err: &int): void

(* ****** ****** *)

fun s2exp_out_void_solve (loc0: loc_t, s2e: s2exp): void
fun s2exp_out_void_solve_at (loc0: loc_t, s2e_at: s2exp): void

(* ****** ****** *)

fun s2exp_equal_solve (_: loc_t, _: s2exp, _: s2exp): void

fun s2exp_equal_solve_err
  (_: loc_t, _: s2exp, _: s2exp, err: &int): void

fun s2explst_equal_solve_err
  (_: loc_t, _: s2explst, _: s2explst, err: &int): void

fun labs2explst_equal_solve_err
  (_: loc_t, _: labs2explst, _: labs2explst, err: &int): void

fun wths2explst_equal_solve_err
  (_: loc_t, _: wths2explst, _: wths2explst, err: &int): void

fun s2explstlst_equal_solve_err
  (_: loc_t, _: s2explstlst, _: s2explstlst, err: &int): void

(* ****** ****** *)

fun s2exp_equal_solve_Var_err
  (_: loc_t, s2V1: s2Var_t, s2e1: s2exp, s2e2: s2exp, err: &int): void

(* ****** ****** *)

fun s2exp_size_equal_solve_err
  (_: loc_t, _: s2exp, _: s2exp, err: &int): void

(* ****** ****** *)

fun s2exp_tyleq_solve (_: loc_t, _: s2exp, _: s2exp): void
fun s2explst_arg_tyleq_solve {n1,n2:nat}
  (_: loc_t, _: s2explst n1, _: s2explst n2): [n1==n2] void

fun s2exp_tyleq_solve_err
  (_: loc_t, _: s2exp, _: s2exp, err: &int): void

fun s2explst_tyleq_solve_err
  (_: loc_t, _: s2explst, _: s2explst, err: &int): void

fun s2explst_tyleq_solve_argvarlst_err
  (_: loc_t,
   s2es1: s2explst,
   s2es2: s2explst,
   argvarlst: List @(symopt_t, s2rt, int), // argument variance list
   err: &int): void

fun labs2explst_tyleq_solve_err
  (_: loc_t, _: labs2explst, _: labs2explst, err: &int): void

fun wths2explst_tyleq_solve_err
  (_: loc_t, _: wths2explst, _: wths2explst, err: &int): void

(* ****** ****** *)

fun s2eff_leq_solve
  (_: loc_t, s2fe1: s2eff, s2fe2: s2eff): void
fun s2eff_leq_solve_err
  (_: loc_t, s2fe1: s2eff, s2fe2: s2eff, err: &int): void

(* ****** ****** *)

fun s2exp_tyleq_solve_Var_l_err
  (_: loc_t, s2V1: s2Var_t, s2e1: s2exp, s2e2: s2exp, err: &int): void
fun s2exp_tyleq_solve_Var_r_err
  (_: loc_t, s2e1: s2exp, s2V2: s2Var_t, s2e2: s2exp, err: &int): void

(* ****** ****** *)

fun s2exp_hypo_equal_solve
  (_: loc_t, s2e1: s2exp, s2e2: s2exp): void
fun s2explst_hypo_equal_solve
  (_: loc_t, s2es1: s2explst, s2es2: s2explst): void

(* ****** ****** *)

(* end of [ats_staexp2_solve.sats] *)
