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

macdef GNULL = (gpointer)null

(* ****** ****** *)

%{^

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menuitem_edit_undo () {
  return theATSUItopenv.menuitem_edit_undo ;
} // end of [atsui_topenv_get_menuitem_edit_undo]

ats_void_type
atsui_topenv_initset_menuitem_edit_undo
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_edit_undo != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_edit_undo] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_edit_undo = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_edit_undo]

ats_ptr_type
atsui_topenv_get_menuitem_edit_redo () {
  return theATSUItopenv.menuitem_edit_redo ;
} // end of [atsui_topenv_get_menuitem_edit_redo]

ats_void_type
atsui_topenv_initset_menuitem_edit_redo
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_edit_redo != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_edit_redo] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_edit_redo = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_edit_redo]

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_menuitem_edit_cut () {
  return theATSUItopenv.menuitem_edit_cut ;
} // end of [atsui_topenv_get_menuitem_edit_cut]

ats_void_type
atsui_topenv_initset_menuitem_edit_cut
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_edit_cut != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_edit_cut] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_edit_cut = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_edit_cut]

ats_ptr_type
atsui_topenv_get_menuitem_edit_copy () {
  return theATSUItopenv.menuitem_edit_copy ;
} // end of [atsui_topenv_get_menuitem_edit_copy]

ats_void_type
atsui_topenv_initset_menuitem_edit_copy
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_edit_copy != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_edit_copy] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_edit_copy = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_edit_copy]

ats_ptr_type
atsui_topenv_get_menuitem_edit_paste () {
  return theATSUItopenv.menuitem_edit_paste ;
} // end of [atsui_topenv_get_menuitem_edit_paste]

ats_void_type
atsui_topenv_initset_menuitem_edit_paste
  (ats_ptr_type x) {
  if (theATSUItopenv.menuitem_edit_paste != (GtkMenuItem*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_menuitem_edit_paste] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.menuitem_edit_paste = (GtkMenuItem*)x ;
} // end of [atsui_topenv_initset_menuitem_edit_paste]

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

fun cb_edit_cut_activate () = let
(*
  val () = (print "cb_edit_cut_activate"; print_newline ())
*)
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val () = g_signal_emit_by_name(tv, (gsignal)"cut-clipboard");
  prval () = fpf_tv (tv)
in
  GTRUE
end // end of [cb_edit_cut_activate]

(* ****** ****** *)

fun cb_edit_copy_activate () = let
(*
  val () = (print "cb_edit_copy_activate"; print_newline ())
*)
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val () = g_signal_emit_by_name(tv, (gsignal)"copy-clipboard");
  prval () = fpf_tv (tv)
in
  GTRUE
end // end of [cb_edit_copy_activate]

(* ****** ****** *)

fun cb_edit_paste_activate () = let
(*
  val () = (print "cb_edit_paste_activate"; print_newline ())
*)
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val () = g_signal_emit_by_name(tv, (gsignal)"paste-clipboard");
  prval () = fpf_tv (tv)
in
  GTRUE
end // end of [cb_edit_paste_activate]

(* ****** ****** *)

implement
topenv_make_menu_edit () = menu where {
  val menu = gtk_menu_new () // to be returned
//
  val undo_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_UNDO)
  val () = gtk_menu_shell_append (menu, undo_item)
  val () = gtk_widget_show (undo_item)
  val () = gtk_widget_set_sensitive (undo_item, GFALSE)
  val () = initset (undo_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_edit_undo"
  } // end of [val]
//
  val redo_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_REDO)
  val () = gtk_menu_shell_append (menu, redo_item)
  val () = gtk_widget_set_sensitive (redo_item, GFALSE)
  val () = gtk_widget_show (redo_item)
  val () = initset (redo_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_edit_redo"
  } // end of [val]
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val cut_item =
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_CUT, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val _sid = g_signal_connect (
    cut_item, (gsignal)"activate", G_CALLBACK(cb_edit_cut_activate), GNULL
  ) // end of [val]
  val () = gtk_menu_shell_append (menu, cut_item)
  val () = gtk_widget_set_sensitive (cut_item, GFALSE)
  val () = gtk_widget_show (cut_item)
  val () = initset (cut_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_edit_cut"
  } // end of [val]
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val copy_item =
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_COPY, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val _sid = g_signal_connect (
    copy_item, (gsignal)"activate", G_CALLBACK(cb_edit_copy_activate), GNULL
  ) // end of [val]
  val () = gtk_menu_shell_append (menu, copy_item)
  val () = gtk_widget_set_sensitive (copy_item, GFALSE)
  val () = gtk_widget_show (copy_item)
  val () = initset (copy_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_edit_copy"
  } // end of [val]
//
  val (fpf_aclgrp | aclgrp) = topenv_get_aclgrp ()
  val paste_item =
    $UT.gtk_image_menu_item_new_from_stock (GTK_STOCK_PASTE, aclgrp)
  prval () = fpf_aclgrp (aclgrp)
  val _sid = g_signal_connect (
    paste_item, (gsignal)"activate", G_CALLBACK(cb_edit_paste_activate), GNULL
  ) // end of [val]
  val () = gtk_menu_shell_append (menu, paste_item)
  val () = gtk_widget_set_sensitive (paste_item, GFALSE)
  val () = gtk_widget_show (paste_item)
  val () = initset (paste_item) where { extern fun initset
    (x: GtkImageMenuItem_ref1): void = "atsui_topenv_initset_menuitem_edit_paste"
  } // end of [val]
//
} // end of [topenv_make_menu_edit]

(* ****** ****** *)

(* end of [atsui_menu_edit.dats] *)
