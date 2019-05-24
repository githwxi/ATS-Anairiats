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
// Time: October 2007
//
(* ****** ****** *)

staload Sym = "ats_symbol.sats"
staload SymEnv = "ats_symenv.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

absview s2rtenv_token
fun the_s2rtenv_add (id: sym_t, s2te: s2rtext): void
//
// HX:
// [find] searches in the following order:
// current env; namespace env; pervasive env
//
fun the_s2rtenv_find (id: sym_t): s2rtextopt_vt
fun the_s2rtenv_find_qua (q: $Syn.s0rtq, id: sym_t): s2rtextopt_vt

fun the_s2rtenv_pop (pf: s2rtenv_token | (*none*)): void
fun the_s2rtenv_push (): (s2rtenv_token | void)

fun the_s2rtenv_localjoin
  (pf1: s2rtenv_token, pf2: s2rtenv_token | (*none*)): void
// end of [the_s2rtenv_localjoin]

(* ****** ****** *)

absview s2expenv_token
fun the_s2expenv_add (id: sym_t, s2i: s2item): void
fun the_s2expenv_add_scst (s2c: s2cst_t): void
fun the_s2expenv_add_svar (s2v: s2var_t): void
fun the_s2expenv_add_svarlst (s2vs: s2varlst): void
fun the_s2expenv_add_datconptr (d2c: d2con_t): void
fun the_s2expenv_add_datcontyp (d2c: d2con_t): void
//
// HX:
// [find] goes in the following order:
// current env; namespace env; pervasive env
//
fun the_s2expenv_find (id: sym_t): s2itemopt_vt
fun the_s2expenv_find_qua (q: $Syn.s0taq, id: sym_t): s2itemopt_vt

fun the_s2expenv_pop (pf: s2expenv_token | (*none*)): void
fun the_s2expenv_push (): (s2expenv_token | void)

fun the_s2expenv_localjoin
  (pf1: s2expenv_token, pf2: s2expenv_token | (*none*)): void
// end of [the_s2expenv_localjoin]

fun the_s2expenv_pervasive_find (id: sym_t): s2itemopt_vt

(* ****** ****** *)

fun macdef_get (): int
fun macdef_inc (): void
fun macdef_dec (): void

fun macro_level_get (): int
fun macro_level_inc (loc: loc_t): void
fun macro_level_dec (loc: loc_t): void

(* ****** ****** *)

fun template_level_get (): int
fun template_level_inc (): void
fun template_level_dec (): void

(* ****** ****** *)

fun s2var_check_tmplev (loc: loc_t, s2v: s2var_t): void
fun s2qualst_set_tmplev (s2vpss: s2qualst, tmplev: int): void

(* ****** ****** *)

absview d2var_current_level_v

fun d2var_current_level_get (): int
fun d2var_current_level_set (n: int): void
fun d2var_current_level_inc (): (d2var_current_level_v | void)
fun d2var_current_level_dec (pf: d2var_current_level_v | (*none*)): void

(* ****** ****** *)

absview d2expenv_token
fun the_d2expenv_add (id: sym_t, d2i: d2item) : void
fun the_d2expenv_add_dcon (d2c: d2con_t): void
fun the_d2expenv_add_dcst (d2c: d2cst_t): void
fun the_d2expenv_add_dmac_def (d2m: d2mac_t): void
fun the_d2expenv_add_dmac_var (d2v: d2var_t): void
fun the_d2expenv_add_dmac_varlst (d2vs: d2varlst): void
fun the_d2expenv_add_dvar (d2v: d2var_t): void
fun the_d2expenv_add_dvarlst (d2vs: d2varlst): void

// HX:
// [find] goes in the following order:
// current env; namespace env; pervasive env
//
fun the_d2expenv_find (id: sym_t): d2itemopt_vt
fun the_d2expenv_find_qua (q: $Syn.d0ynq, id: sym_t): d2itemopt_vt

fun the_d2expenv_pop (pf: d2expenv_token | (*none*)): void
fun the_d2expenv_push (): (d2expenv_token | void)
fun the_d2expenv_swap (r_map: $SymEnv.symmapref d2item): void
fun the_d2expenv_localjoin
  (pf1: d2expenv_token, pf2: d2expenv_token | (*none*)): void
// end of [the_d2expenv_localjoin]

fun the_d2expenv_current_find (id: sym_t): d2itemopt_vt
fun the_d2expenv_pervasive_find (id: sym_t): d2itemopt_vt

(* ****** ****** *)

absview staload_level_token
fun staload_level_get_level (): int
fun staload_level_push (): (staload_level_token | void)
fun staload_level_pop (pf: staload_level_token | (*none*)): void

(* ****** ****** *)

fun d2eclst_namespace_add (_: sym_t, _: d2eclst): void
fun d2eclst_namespace_find (_: sym_t): Option_vt (d2eclst)

(* ****** ****** *)

absview trans2_env_token
fun trans2_env_pop (pf: trans2_env_token | (*none*)): void
fun trans2_env_push (): (trans2_env_token | void)

fun trans2_env_localjoin
  (pf1: trans2_env_token, pf2: trans2_env_token | (*none*)): void
// end of [trans2_env_localjoin]

fun trans2_env_save (): void
fun trans2_env_restore (): void

fun trans2_env_pervasive_add_topenv (): void
fun trans2_env_namespace_add_topenv (id: sym_t): void

(* ****** ****** *)

fun trans2_env_initize (): void

(* ****** ****** *)

(* end of [ats_trans2_env.dats] *)
