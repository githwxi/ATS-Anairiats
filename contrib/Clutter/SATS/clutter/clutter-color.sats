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

typedef ClutterColor =
  $extype_struct "ClutterColor" of {
  red= guint8
, green= guint8
, blue= guint8
, alpha= guint8
} // end of [ClutterColor]

(* ****** ****** *)

fun clutter_color_new (
  red: guint8, green: guint, blue: guint, alpha: guint
) : [l:addr] (
  ClutterFree_v l, ClutterColor @ l | ptr l
) = "mac#atsctrb_clutter_color_new"
// end of [clutter_color_new]

fun clutter_color_copy (
  color: &ClutterColor
) : [l:addr] (
  ClutterFree_v l, ClutterColor @ l | ptr l
) = "mac#atsctrb_clutter_color_copy"
// end of [clutter_color_copy]

fun clutter_color_free {l:addr}
  (pf1: ClutterFree_v l, pf2: ClutterColor? @ l | p: ptr l): void
  = "mac#atsctrb_clutter_color_free"
// end of [clutter_color_free]

(* ****** ****** *)

(* end of [clutter-color.sats] *)
