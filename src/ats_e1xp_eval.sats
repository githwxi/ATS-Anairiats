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
// Time: October 2007

(* ****** ****** *)

staload Loc = "ats_location.sats"
staload Syn = "ats_syntax.sats"
staload SEXP = "ats_staexp1.sats"

(* ****** ****** *)

fun v1al_is_true (v: $SEXP.v1al): bool
fun v1al_is_false (v: $SEXP.v1al): bool
fun e1xp_eval (e: $SEXP.e1xp): $SEXP.v1al
fun e1xp_eval_if (knd: $Syn.srpifkind, e: $SEXP.e1xp): $SEXP.v1al
fun e1xp_make_v1al (loc: $Loc.location_t, v: $SEXP.v1al): $SEXP.e1xp

(* ****** ****** *)

(* end of [ats_e1xp_eval.sats] *)
