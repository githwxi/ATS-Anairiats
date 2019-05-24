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

staload "contrib/pango/SATS/pango.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"

(* ****** ****** *)

macdef GNULL = (gpointer)null
macdef gs = gstring_of_string

(* ****** ****** *)

%{^

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_statusbar () {
  return theATSUItopenv.statusbar ;
} // end of [atsui_topenv_get_statusbar]

ats_void_type
atsui_topenv_initset_statusbar
  (ats_ptr_type x) {
  if (theATSUItopenv.statusbar != (GtkStatusbar*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_statusbar] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.statusbar = (GtkStatusbar*)x ;
} // end of [atsui_topenv_initset_statusbar]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menuitem_view_fontsel () {
  return theATSUItopenv.menuitem_view_fontsel ;
} // end of [atsui_topenv_get_menuitem_view_fontsel]

ats_void_type
atsui_topenv_initset_menuitem_view_fontsel
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_view_fontsel != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_view_fontsel] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_view_fontsel = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_view_fontsel]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menuitem_view_linenumber () {
  return theATSUItopenv.menuitem_view_linenumber ;
} // end of [atsui_topenv_get_menuitem_view_linenumber]

ats_void_type
atsui_topenv_initset_menuitem_view_linenumber
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_view_linenumber != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_view_linenumber] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_view_linenumber = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_view_linenumber]

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

fun toggle_statusbar
  (tf: gboolean) = () where {
  val tf = (bool_of)tf
  val (fpf_bar | bar) = topenv_get_statusbar ()
  val () = (
    if tf then gtk_widget_show (bar) else gtk_widget_hide (bar)
  ) : void
  prval () = fpf_bar (bar)
} // end of [cb_toggle_statusbar]

fun cb_view_statusbar_activate {l:agz}
  (item: !GtkCheckMenuItem_ref l)
  : gboolean = GTRUE where {
  val active = gtk_check_menu_item_get_active (item)
  val () = toggle_statusbar (active)
} // end of [cb_view_statusbar]

(* ****** ****** *)

implement
topenv_make_menu_view () = menu where {
  val menu = gtk_menu_new () // to be returned
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val fontsel_item =
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_SELECT_FONT, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val (fpf_x | x) = (gs)"_Font..."
  val () = gtk_menu_item_set_label (fontsel_item, x)
  prval () = fpf_x (x)
  val _sig = g_signal_connect
    (fontsel_item, (gsignal)"activate", G_CALLBACK(cb_view_fontsel_activate), GNULL)
  val () = gtk_menu_shell_append (menu, fontsel_item)
  val () = gtk_widget_set_sensitive (fontsel_item, GFALSE)
  val () = gtk_widget_show (fontsel_item)
  val () = initset (fontsel_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_view_fontsel"
  } // end of [val]
//
  val (fpf_x | x) = (gs)"Status Bar"
  val statusbar_item = gtk_check_menu_item_new_with_label (x)
  prval () = fpf_x (x)
  val () = gtk_check_menu_item_set_active (statusbar_item, GFALSE)
  val _sid = g_signal_connect
    (statusbar_item, (gsignal)"activate", G_CALLBACK(cb_view_statusbar_activate), GNULL)
  val () = gtk_menu_shell_append (menu, statusbar_item)
  val () = gtk_widget_show_unref (statusbar_item)
//
  val (fpf_x | x) = (gs)"Line Numbers"
  val linenumber_item = gtk_check_menu_item_new_with_label (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect (
    linenumber_item, (gsignal)"activate", G_CALLBACK(cb_view_linenumber_activate), GNULL
  ) // end of [val]
  val () = gtk_check_menu_item_set_active (linenumber_item, GFALSE) // HX: should it?
  val () = gtk_menu_shell_append (menu, linenumber_item)
  val () = gtk_widget_set_sensitive (linenumber_item, GFALSE)
  val () = gtk_widget_show (linenumber_item)
  val () = initset (linenumber_item) where { extern fun initset
    (x: GtkCheckMenuItem_ref1): void = "atsui_topenv_initset_menuitem_view_linenumber"
  } // end of [val]
//
} // end of [topenv_make_menu_view]

(* ****** ****** *)

(* end of [atsui_menu_view.dats] *)
