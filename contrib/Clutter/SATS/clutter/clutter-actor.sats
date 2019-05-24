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
// Start Time: June, 2010
//
(* ****** ****** *)

fun clutter_actor_show
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void = "mac#atsctrb_clutter_actor_show"
// end of [clutter_actor_show]

fun clutter_actor_show_all
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void = "mac#atsctrb_clutter_actor_show_all"
// end of [clutter_actor_show_all]

(* ****** ****** *)

fun clutter_actor_hide
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void = "mac#atsctrb_clutter_actor_hide"
// end of [clutter_actor_hide]

fun clutter_actor_hide_all
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void = "mac#atsctrb_clutter_actor_hide_all"
// end of [clutter_actor_hide_all]

(* ****** ****** *)

fun clutter_actor_map
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void = "mac#atsctrb_clutter_actor_map"
// end of [clutter_actor_map]

fun clutter_actor_unmap
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void = "mac#atsctrb_clutter_actor_unmap"
// end of [clutter_actor_unmap]

(* ****** ****** *)

fun clutter_actor_realize
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void = "mac#atsctrb_clutter_actor_realize"
// end of [clutter_actor_realize]

fun clutter_actor_unrealize
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void = "mac#atsctrb_clutter_actor_unrealize"
// end of [clutter_actor_unrealize]

(* ****** ****** *)

fun clutter_actor_paint
  {c:cls | c <= ClutterActor}
  {l:agz} (
  self: !gobjref (c, l)
) : void
  = "mac#atsctrb_clutter_actor_paint"
// end of [clutter_actor_paint]

(* ****** ****** *)

fun clutter_actor_queue_redraw
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void
  = "mac#atsctrb_clutter_actor_queue_redraw"
// end of [clutter_actor_queue_redraw]

fun clutter_actor_queue_relayout
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): void
  = "mac#atsctrb_clutter_actor_queue_relayout"
// end of [clutter_actor_queue_relayout]

(* ****** ****** *)

fun clutter_actor_get_width
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): gfloat
  = "mac#atsctrb_clutter_actor_get_width"
// end of [clutter_actor_get_width]

fun clutter_actor_set_width
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l), width: gfloat): void
  = "mac#atsctrb_clutter_actor_set_width"
// end of [clutter_actor_set_width]

fun clutter_actor_get_height
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l)): gfloat = "mac#atsctrb_clutter_actor_get_height"
// end of [clutter_actor_get_height]

fun clutter_actor_set_height
  {c:cls | c <= ClutterActor} {l:agz}
  (self: !gobjref (c, l), height: gfloat): void
  = "mac#atsctrb_clutter_actor_set_height"
// end of [clutter_actor_set_height]

fun clutter_actor_get_size
  {c:cls | c <= ClutterActor} {l:agz} (
    self: !gobjref (c, l), w: &gfloat? >> gfloat, h: &gfloat? >> gfloat
  ) : void = "mac#atsctrb_clutter_actor_get_size"
// end of [clutter_actor_get_size]

fun clutter_actor_set_size
  {c:cls | c <= ClutterActor}
  {l:agz} (
  self: !gobjref (c, l), w: gfloat, h: gfloat
) : void
  = "mac#atsctrb_clutter_actor_set_size"
// end of [clutter_actor_set_size]

(* ****** ****** *)

fun clutter_actor_get_position
  {c:cls | c <= ClutterActor}
  {l:agz} (
  self: !gobjref (c, l)
, x: &gfloat? >> gfloat, y: &gfloat? >> gfloat
) : void
  = "mac#atsctrb_clutter_actor_get_position"
// end of [clutter_actor_get_position]

fun clutter_actor_set_position
  {c:cls | c <= ClutterActor}
  {l:agz} (
  self: !gobjref (c, l), x: gfloat, y: gfloat
) : void
  = "mac#atsctrb_clutter_actor_set_position"
// end of [clutter_actor_set_position]

(* ****** ****** *)

(* end of [clutter-actor.sats] *)
