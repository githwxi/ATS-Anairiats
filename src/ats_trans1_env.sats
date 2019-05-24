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
(* ****** ******* *)

staload Fix = "ats_fixity.sats"
typedef fxty = $Fix.fxty
staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t

(* ****** ******* *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ******* *)

fun the_e1xpenv_add (id: sym_t, _: e1xp): void
fun the_e1xpenv_find (id: sym_t): Option_vt e1xp
fun the_e1xpenv_pervasive_add_topenv (): void

(* ****** ******* *)

fun the_fxtyenv_add (id: sym_t, _: fxty): void
fun the_fxtyenv_find (id: sym_t): Option_vt (fxty)
fun the_fxtyenv_pervasive_add_topenv (): void

(* ****** ******* *)

fun atsopt_fxtyenv_print (): void // mostly for debugging

(* ****** ******* *)

(*
//
// HX-2014-07:
// these functions are no longer in use
//
absview
trans1_level_v // for avoiding negative levels
fun trans1_level_get (): int
fun trans1_level_dec (pf: trans1_level_v | (*none*)): void
fun trans1_level_inc (): (trans1_level_v | void)
*)

(* ****** ******* *)

fun trans1_env_pop (): void
fun trans1_env_push (): void

(*
** HX: for handling <local ... in ... end>
*)
fun trans1_env_localjoin (): void

fun trans1_env_save (): void
fun trans1_env_restore (): void

(* ****** ******* *)

fun staload_file_insert
  (fullname: string, flag: int, d1cs: d1eclst): void
fun staload_file_search
  (fullname: string): Option_vt @(int(*flag*), d1eclst)

(* ****** ******* *)

(* end of [ats_trans1_env.sats] *)
