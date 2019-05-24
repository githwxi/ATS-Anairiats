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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May 2010

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"

(* ****** ****** *)

%{^

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menu_window () {
  return theATSUItopenv.menu_window ;
} // end of [atsui_topenv_get_menu_window]

ats_void_type
atsui_topenv_initset_menu_window
  (ats_ptr_type x) {
  if (theATSUItopenv.menu_window != (GtkMenu*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menu_window] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menu_window = (GtkMenu*)x ;
} // end of [atsui_topenv_initset_menu_window]

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

implement
topenv_make_menu_window () = menu where {
  val menu = gtk_menu_new () // it appears on the menubar
//
  val item = $UT.gtk_menu_item_new_with_label ("Window List...")
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show_unref (item)
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
} // end of [topenv_make_menu_window]

(* ****** ****** *)

fun cb_menu_window_item
  {c:cls | c <= GtkTextBuffer} {l:agz}
  (tb: !gobjref (c, l)): gboolean = GTRUE where {
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val () = gtk_text_view_set_buffer (tv, tb)
  prval () = fpf_tv (tv)
  val () = topenv_container_source_update_label ()
} // end of [cb_menu_window_item]

(* ****** ****** *)

implement
topenv_menu_window_append {c} (filename, tb) = let
//
  prval () = clstrans {c,GtkTextBuffer,GObject} ()
//
  val (fpf_menu | menu) = topenv_get_menu_window ()
  val item = gtk_menu_item_new_with_label (filename)
  val _sid = g_signal_connect_swapped (
    item, (gsignal)"activate", G_CALLBACK(cb_menu_window_item), tb
  )
  val () = gtk_menu_shell_append (menu, item)
  val () = gtk_widget_show (item)
  prval () = fpf_menu (menu)
in
  item
end // end of [topenv_menu_window_append]

(* ****** ****** *)

implement
topenv_menu_window_remove
  {c} (item) = () where {
  val (fpf_menu | menu) = topenv_get_menu_window ()
//
  prval () = clstrans {c,GtkMenuItem,GtkWidget} ()
//
  val () = gtk_container_remove (menu, item)
  prval () = fpf_menu (menu)
} // end of [topenv_menu_window_remove]

(* ****** ****** *)

(* end of [atsui_menu_winlst.dats] *)
