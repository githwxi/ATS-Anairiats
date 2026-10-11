(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
// Time: April, 2010
//
(* ****** ****** *)

fun gtk_main
  (): void = "mac#atsctrb_gtk_main"
// end of [gtk_main]

fun gtk_main_level
  (): guint = "mac#atsctrb_gtk_main_level"
// end of [gtk_main_level]

(*
// gtk_main_iteration(): gtk_main_iteration_do(TRUE)
*)
fun gtk_main_iteration
  (): gboolean = "mac#gtk_main_iteration"
fun gtk_main_iteration_do
  (blocking: gboolean): gboolean = "mac#gtk_main_iteration_do"
// end of [gtk_main_iteration_do]

fun gtk_main_quit (): void = "mac#atsctrb_gtk_main_quit"

(* ****** ****** *)

fun gtk_init_add (
  f: GtkFunction, data: gpointer
) : void = "mac#gtk_init_add" // end of [gtk_init_add]

fun gtk_quit_add (
  level: guint, f: GtkFunction, data: gpointer
) : guint = "mac#gtk_quit_add" // end of [gtk_quit_add]

(* ****** ****** *)

fun gtk_events_pending
  ((*none*)): gboolean = "mac#gtk_events_pending"
// end of [gtk_events_pending]

(* ****** ****** *)

#ifndef
GTK_DISABLE_DEPRECATED
#then

fun
gtk_timeout_add (
  interval: guint32
, f: GtkFunction, data: gpointer
) : guint
  = "mac#atsctrb_gtk_timeout_add"
// end of [gtk_timeout_add]

fun gtk_timeout_remove
  (id: guint): void = "mac#gtk_timeout_remove"
// end of [gtk_timeout_remove]

#endif // end of [...]

(* ****** ****** *)

(* end of [gtkmain.sats] *)
