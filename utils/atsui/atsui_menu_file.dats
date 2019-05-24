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
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"

(* ****** ****** *)

macdef gs = gstring_of_string
macdef GNULL = (gpointer)null

(* ****** ****** *)

%{^

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menu_file () {
  return theATSUItopenv.menu_file ;
} // end of [atsui_topenv_get_menu_file]

ats_void_type
atsui_topenv_initset_menu_file
  (ats_ptr_type x) {
  if (theATSUItopenv.menu_file != (GtkMenu*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menu_file] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menu_file = (GtkMenu*)x ;
} // end of [atsui_topenv_initset_menu_file]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menuitem_file_close () {
  return theATSUItopenv.menuitem_file_close ;
} // end of [atsui_topenv_get_menuitem_file_close]

ats_void_type
atsui_topenv_initset_menuitem_file_close
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_file_close != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_file_close] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_file_close = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_file_close]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menuitem_file_save () {
  return theATSUItopenv.menuitem_file_save ;
} // end of [atsui_topenv_get_menuitem_file_save]

ats_void_type
atsui_topenv_initset_menuitem_file_save
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_file_save != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_file_save] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_file_save = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_file_save]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menuitem_file_saveas () {
  return theATSUItopenv.menuitem_file_saveas ;
} // end of [atsui_topenv_get_menuitem_file_saveas]

ats_void_type
atsui_topenv_initset_menuitem_file_saveas
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_file_saveas != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_file_saveas] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_file_saveas = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_file_saveas]

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

%{^

int theScratchCount = 1;
ats_int_type
atsui_theScratchCount_getinc () {
  int n = theScratchCount ; theScratchCount += 1 ; return n ;
} // end of [atsui_theScratchCount_getinc]

%} // end of [%{]

extern
fun theScratchCount_getinc
  (): int = "atsui_theScratchCount_getinc"
// end of [theScratchCount_getinc]

fun cb_new_activate
  (): gboolean = GTRUE where {
//
  val () = (print (#LOCATION + ": cb_new_activate"); print_newline ())
//
  val () = topenv_initset_textview_source_if () // create and set it if not existent
//
  val tb = gtk_text_buffer_new_null ()
  val _sid = g_signal_connect
    (tb, (gsignal)"mark-set", G_CALLBACK(cb_textview_source_mark_changed), GNULL)
  val _sid = g_signal_connect
    (tb, (gsignal)"modified-changed", G_CALLBACK(cb_textview_source_modified_changed), GNULL)
  val () = gtk_text_buffer_set_modified (tb, GFALSE)
//
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val () = gtk_text_view_set_editable (tv, GTRUE)
  val () = gtk_text_view_set_cursor_visible (tv, GTRUE)
  val () = gtk_text_view_set_buffer (tv, tb)
  val n = theScratchCount_getinc ()
  val filename = g_strdup_printf ("scratch%3.3i.dats", @(n))
  val item = topenv_menu_window_append (filename, tb)
  val srcwin = $SWL.srcwin_make (filename, tb, item)
  val () = $SWL.the_srcwinlst_append (srcwin)
  prval () = fpf_tv (tv)
//
  val () = topenv_container_source_update_label () // HX: could be more efficient, but ...
  val _true = cb_textview_source_modified_changed ()
//
} // end of [cb_new_activate]

(* ****** ****** *)

fun cb_close_activate (): gboolean = let
//
  val () = (print (#LOCATION + ": cb_close_activate"); print_newline ())
//
// val () = topenv_textview_source_initset_if () // already set at this point
//
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
  var n: int
  val x = $SWL.the_srcwinlst_remove (tb, n)
  val px = $SWL.ptr_of_srcwin (x)
  val () = if (px > null) then let
    val (fpf_menuitm | menuitm) = $SWL.srcwin_get_menuitm (x)
    val () = topenv_menu_window_remove (menuitm)
    prval () = minus_addback (fpf_menuitm, menuitm | x)
    val () = $SWL.srcwin_free (x)
  in
    // nothing
  end else let
    val _null = $SWL.srcwin_free_null x
  in
    // nothing
  end // end of [val]
  prval () = minus_addback (fpf_tb, tb | tv)
  var px: Ptr = null
  val n = int1_of_int (n)
  val () = if n >= 0 then let
    val (fpf_x | x) = $SWL.the_srcwinlst_getnext (n)
    val () = px := $SWL.ptr_of_srcwin x
    val () = if px > null then let
      val (fpf_tb | tb) = $SWL.srcwin_get_textbuf (x)
      val () = gtk_text_view_set_buffer (tv, tb)
      prval () = minus_addback (fpf_tb, tb | x)
    in
      // nothing
    end (* end of [if] *)
    prval () = fpf_x (x)
  in
    // nothing
  end // end of [val]
  prval () = fpf_tv (tv)
  val () = if (px > null) then topenv_container_source_update_label ()
in
  if px = null then cb_new_activate () else GTRUE
end // end of [cb_close_activate]

(* ****** ****** *)

implement
topenv_make_menu_file () = menu where {
  val menu = gtk_menu_new () // to be returned
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val new_item =
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_NEW, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val _sid = g_signal_connect (
    new_item, (gsignal)"activate", G_CALLBACK(cb_new_activate), GNULL
  ) // end of [val]
  val () = gtk_menu_shell_append (menu, new_item)
  val () = gtk_widget_show_unref (new_item)
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val openfile_item =
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_OPEN, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val (fpf_x | x) = (gs)"Open File..."
  val () = gtk_menu_item_set_label (openfile_item, x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect (
    openfile_item, (gsignal)"activate", G_CALLBACK(cb_file_openfile_activate), GNULL
  ) // end of [val]
  val () = gtk_menu_shell_append (menu, openfile_item)
  val () = gtk_widget_show_unref (openfile_item)
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val close_item =
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_CLOSE, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val _sid = g_signal_connect (
    close_item, (gsignal)"activate", G_CALLBACK(cb_close_activate), GNULL
  ) // end of [val]
  val () = gtk_menu_shell_append (menu, close_item)
  val () = gtk_widget_set_sensitive (close_item, GFALSE)
  val () = gtk_widget_show (close_item)
  val () = initset (close_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_file_close"
  } // end of [val]
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val save_item =
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_SAVE, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val _sid = g_signal_connect (
    save_item, (gsignal)"activate", G_CALLBACK(cb_file_save_activate), GNULL
  ) // end of [val]
  val () = gtk_menu_shell_append (menu, save_item)
  val () = gtk_widget_set_sensitive (save_item, GFALSE)
  val () = gtk_widget_show (save_item)
  val () = initset (save_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_file_save"
  } // end of [val]
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val saveas_item = 
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_SAVE_AS, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val _sid = g_signal_connect (
    saveas_item, (gsignal)"activate", G_CALLBACK(cb_file_saveas_activate), GNULL
  ) // end of [val]
  val () = gtk_menu_shell_append (menu, saveas_item)
  val () = gtk_widget_set_sensitive (saveas_item, GFALSE)
  val () = gtk_widget_show (saveas_item)
  val () = initset (saveas_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_file_saveas"
  } // end of [val]
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val quit_item = $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_QUIT, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val _sid = g_signal_connect
    (quit_item, (gsignal)"activate", G_CALLBACK(cb_file_quit_activate), GNULL)
  val () = gtk_menu_shell_append (menu, quit_item)
  val () = gtk_widget_show_unref (quit_item)
//
} // end of [topenv_make_menu_file]

(* ****** ****** *)

(* end of [atsui_menu_file.dats] *)
