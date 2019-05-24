(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2009-2010 Hongwei Xi, Boston University
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
// Time: June, 2010
//
(* ****** ****** *)

fun clutter_actor_add_action
  {c1,c2:cls | c1 <= ClutterActor; c2 <= ClutterAction}
  {l1,l2:agz} (self: !gobjref (c1, l1), action: !gobjref (c2, l2)): void
  = "mac#atsctrb_clutter_actor_add_action"
// end of [clutter_actor_add_action]

fun clutter_actor_remove_action
  {c1,c2:cls | c1 <= ClutterActor; c2 <= ClutterAction}
  {l1,l2:agz} (self: !gobjref (c1, l1), action: !gobjref (c2, l2)): void
  = "mac#atsctrb_clutter_actor_remove_action"
// end of [clutter_actor_remove_action]

fun clutter_actor_clear_actions
  {c:cls | c <= ClutterActor} {l:agz} (self: !gobjref (c, l)): void
  = "mac#atsctrb_clutter_actor_clear_actions"
// end of [clutter_actor_clear_actions]

(* ****** ****** *)

(* end of [clutter-action.sats] *)
