(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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
// Start Time: February, 2011
//
(* ****** ****** *)

%{#
#include "contrib/linux/linux/CATS/module.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)
//
// HX: this is ref-counted
//
absviewtype module_ref (l:addr)
viewtypedef module_ref1 = [l:agz] module_ref (l)
//
(* ****** ****** *)

abst@ype
module_state = $extype "module_state"
macdef MODULE_STATE_LIVE =
  $extval (module_state, "MODULE_STATE_LIVE")
macdef MODULE_STATE_COMING =
  $extval (module_state, "MODULE_STATE_COMING")
macdef MODULE_STATE_GOING =
  $extval (module_state, "MODULE_STATE_GOING")

(* ****** ****** *)

(* end of [module.sats] *)
