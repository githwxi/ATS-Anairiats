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

abst@ype
ClutterInitError = $extype"ClutterInitError"
macdef CLUTTER_INIT_SUCCESS = $extval (ClutterInitError, "CLUTTER_INIT_SUCCESS")
macdef CLUTTER_INIT_UNKNOWN = $extval (ClutterInitError, "CLUTTER_INIT_UNKNOWN")
macdef CLUTTER_INIT_THREADS = $extval (ClutterInitError, "CLUTTER_INIT_THREADS")
macdef CLUTTER_INIT_BACKEND = $extval (ClutterInitError, "CLUTTER_INIT_BACKEND")
macdef CLUTTER_INIT_INTERNAL = $extval (ClutterInitError, "CLUTTER_INIT_INTERNAL")

(* ****** ****** *)

fun clutter_main (): void = "mac#atsctrb_clutter_main"
fun clutter_main_quit (): void = "mac#atsctrb_clutter_main_quit"
fun clutter_main_level (): gint = "mac#atsctrb_clutter_main_level"

(* ****** ****** *)

(* end of [clutter-main.sats] *)