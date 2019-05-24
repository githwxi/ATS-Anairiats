(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2010-201? Hongwei Xi, Boston University
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
// Time: May, 2010
//
(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"
macdef gs = gstring_of_string
overload gint with gint_of_GtkResponseType

(* ****** ****** *)

implement
cb_file_quit_activate () = GTRUE where {
//
  val () = (print (#LOCATION + ": cb_quit_activate"); print_newline ())
//
  val flags = GTK_DIALOG_DESTROY_WITH_PARENT
  val _type = GTK_MESSAGE_QUESTION
  val buttons = GTK_BUTTONS_YES_NO
//
  val (fpf_x | x) = (gs)"Quit ATSUI?"
  val dialog = gtk_message_dialog_new0 (flags, _type, buttons, x)
  prval () = fpf_x (x)
  val (fpf_x | x) = (gs)"Confirmation"
  val () = gtk_window_set_title (dialog, x)
  prval () = fpf_x (x)
//
  val (fpf_topwin | topwin) = topenv_get_topwin ()
  val () = gtk_window_set_transient_for (dialog, topwin(*parent*))
  prval () = fpf_topwin (topwin)
//
  val response = gtk_dialog_run (dialog)
  val () = gtk_widget_destroy0 (dialog)
//
  val () = case+ 0 of
    | _ when response = (gint)GTK_RESPONSE_YES => topenv_fini () // many things to do here!
    | _ => () // quit is not confirmed
  // end of [val]
} // end of [cb_file_quit_activate]

(* ****** ****** *)

(* end of [atsui_menuite_file_quit.dats] *)
