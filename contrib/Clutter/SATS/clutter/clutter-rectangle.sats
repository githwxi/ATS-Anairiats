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

fun clutter_rectangle_new
  (): ClutterRectangle_ref1 = "mac#atsctrb_clutter_rectangle_new"
// end of [clutter_rectangle_new]

fun clutter_rectangle_new_with_color
  (clr: &ClutterColor): ClutterRectangle_ref1
  = "mac#atsctrb_clutter_rectangle_new_with_color"
// end of [clutter_rectangle_new_with_color]

(* ****** ****** *)

fun clutter_rectangle_get_color
  {c:cls | c <= ClutterRectangle} {l:agz}
  (rect: !gobjref (c, l), clr: &ClutterColor? >> ClutterColor): void
  = "mac#atsctrb_clutter_rectangle_get_color"
// end of [clutter_rectangle_get_color]

fun clutter_rectangle_set_color
  {c:cls | c <= ClutterRectangle} {l:agz}
  (rect: !gobjref (c, l), clr: &ClutterColor): void
  = "mac#atsctrb_clutter_rectangle_set_color"
// end of [clutter_rectangle_set_color]

(* ****** ****** *)

(* end of [clutter-rectangle.sats] *)
