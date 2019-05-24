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

(* Mainly for handling macro expansion during type-checking *)

(* ****** ****** *)

staload Loc = "ats_location.sats"
staload DEXP2 = "ats_dynexp2.sats"

(* ****** ****** *)

// for expanding macros
fun macro_eval_cross (d2e: $DEXP2.d2exp): $DEXP2.d2exp
fun macro_eval_decode (d2e: $DEXP2.d2exp): $DEXP2.d2exp

// for expanding macros in short form
fun macro_eval_app_short
  (loc0: $Loc.location_t, d2m: $DEXP2.d2mac_t, d2as: $DEXP2.d2exparglst)
  : $DEXP2.d2exp
// end of [macro_eval_app_short]

(* ****** ****** *)

(* end of [ats_macro2.sats] *)
