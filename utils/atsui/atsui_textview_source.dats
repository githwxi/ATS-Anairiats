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

staload "contrib/pango/SATS/pango.sats"

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
atsui_topenv_get_textview_source () {
  return theATSUItopenv.textview_source ;
} // end of [atsui_topenv_get_textview_source]

static
int the_topenv_textview_source_initset_flag = 0 ;

ats_void_type
atsui_topenv_initset_textview_source
  (ats_ptr_type x) {
  the_topenv_textview_source_initset_flag = 1 ;
  theATSUItopenv.textview_source = (GtkTextView*)x ;
} // end of [atsui_topenv_initset_textview_source]

ats_int_type
atsui_topenv_get_textview_source_initset_flag
  () { return the_topenv_textview_source_initset_flag ; }
// end of [atsui_topenv_get_textview_source_initset_flag]

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

implement
topenv_textview_source_update_statusbar
  () = () where {
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
//
  val isModified = gtk_text_buffer_get_modified (tb)
  val isModified = (bool_of)isModified
  val YN = (if isModified then 'Y' else 'N'): char
//
  val (fpf_tm | tm) = gtk_text_buffer_get_insert (tb)
  var iter: GtkTextIter
  val () = gtk_text_buffer_get_iter_at_mark (tb, iter, tm)
  prval () = minus_addback (fpf_tm, tm | tb)
  val nrow = gtk_text_iter_get_line (iter)
  val nrow = int_of_gint (nrow)
  val ncol = gtk_text_iter_get_line_offset (iter)
  val ncol = int_of_gint (ncol)
//
  val (fpf_bar | bar) = topenv_get_statusbar ()
  val () = gtk_statusbar_pop (bar, (guint)0)
  val msg = g_strdup_printf
    ("--modified(%c)--line/col(%i/%i)--", @(YN, nrow+1, ncol+1))
  val _mid = gtk_statusbar_push (bar, (guint)0, msg)
  val () = gstring_free (msg)
  prval () = fpf_bar (bar)
  prval () = minus_addback (fpf_tb, tb | tv)
  prval () = fpf_tv (tv)
} // end of [topenv_textview_source_update_statusbar]

(* ****** ****** *)

fun menu_sensitivity_from_selection_bound
  (isBoundExist: gboolean): void = () where {
  val (fpf_item | item) = topenv_get_menuitem_edit_cut ()
  val () = gtk_widget_set_sensitive(item, isBoundExist)
  prval () = fpf_item (item)
  val (fpf_item | item) = topenv_get_menuitem_edit_copy ()
  val () = gtk_widget_set_sensitive(item, isBoundExist)
  prval () = fpf_item (item)
} // end of [menu_sensitivity_from_selection_bound]

fun menu_sensitivity_from_clipboard
  (): void = () where {
// (*
  val () = (print "menu_sensitivity_from_clipboard"; print_newline ())
// *)
  val (fpf_clip | clip) = gtk_clipboard_get (GDK_SELECTION_CLIPBOARD)
  val (fpf_item | item) = topenv_get_menuitem_edit_paste ()
  val isAvailable = gtk_clipboard_wait_is_text_available (clip)
  val () = gtk_widget_set_sensitive (item, isAvailable)
  prval () = fpf_item (item)
  prval () = fpf_clip (clip)
} // end of [menu_sensitivity_from_clipboard]

fun menu_sensitivity_from_modified_flag
  (isModified: gboolean): void = () where {
  val (fpf_item | item) = topenv_get_menuitem_file_save ()
  val () = gtk_widget_set_sensitive (item, isModified)
  prval () = fpf_item (item)
} // end of [menu_sensitivity_from_modified_flag]

(* ****** ****** *)

implement
cb_textview_source_mark_changed () = let
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
  val isBoundExist = gtk_text_buffer_get_selection_bounds_null (tb)
  prval () = minus_addback (fpf_tb, tb | tv)
  prval () = fpf_tv (tv)
  val () = menu_sensitivity_from_selection_bound (isBoundExist)
  val () = topenv_textview_source_update_statusbar ()
in
  GTRUE // it is called last
end // end of [cb_textview_source_mark_changed]

implement
cb_textview_source_modified_changed () = let
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
  val isModified = gtk_text_buffer_get_modified (tb)
  prval () = minus_addback (fpf_tb, tb | tv)
  prval () = fpf_tv (tv)
  val () = menu_sensitivity_from_modified_flag (isModified)
in
  GTRUE // it is called last
end // end of [cb_textview_source_modified_changed]

(* ****** ****** *)

// "Comic sans MS 10"
#define TEXTVIEW_SOURCE_FONT "Courier 12" // a font of fixed-size
#define TEXTVIEW_SOURCE_LEFT_MARGIN 6

extern
fun topenv_make_textview_source (): GtkTextView_ref1
implement
topenv_make_textview_source () = let
  val tb = gtk_text_buffer_new_null ()
  val tv = gtk_text_view_new_with_buffer (tb)
  val () = g_object_unref (tb)
  // val () = gtk_widget_grab_focus (tv) // HX: what does this mean?
//
  val _sid = g_signal_connect (
    tv, (gsignal)"expose_event", G_CALLBACK(cb_textview_source_expose_event_linenumber), GNULL
  ) // end of [val]
//
  val (fpf_name | name) = __cast (TEXTVIEW_SOURCE_FONT) where {
    extern castfn __cast (x: string): [l:agz] (gstring l -<lin,prf> void | gstring l)
  } // end of [val]
  val fd = pango_font_description_from_string (name)
//
  val pfd = ptr_of (fd)
  val () = (print "pfd = "; print pfd; print_newline ())
  val () = gtk_widget_modify_font (tv, fd)
//
  val () = pango_font_description_free (fd)
  prval () = fpf_name (name)
  val () = gtk_text_view_set_editable (tv, GFALSE)
  val () = gtk_text_view_set_cursor_visible (tv, GFALSE)
  val () = gtk_text_view_set_left_margin (tv, (gint)TEXTVIEW_SOURCE_LEFT_MARGIN)
in
  tv (* return *)
end // end of [topenv_make_textview_source]

(* ****** ****** *)

implement
topenv_initset_textview_source_if () = let
  val tvflag = topenv_get_textview_source_initset_flag ()
in
//
if tvflag = 0 then let
  val win = gtk_scrolled_window_new_null ()
  val () = gtk_scrolled_window_set_policy
    (win, GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC)
  val tv = topenv_make_textview_source ()
//
  val _sid = g_signal_connect_after
    (tv, (gsignal)"cut-clipboard", G_CALLBACK(menu_sensitivity_from_clipboard), GNULL)
  val _sid = g_signal_connect_after
    (tv, (gsignal)"copy-clipboard", G_CALLBACK(menu_sensitivity_from_clipboard), GNULL)
//
  val () = gtk_container_add (win, tv)
  val () = gtk_widget_show (tv)
  val () = initset (tv) where { extern fun initset
    (x: GtkTextView_ref1): void = "atsui_topenv_initset_textview_source"
  } // end of [val]
//
// HX: enabling the CLOSE, SAVE and SAVEAS menu items
//
  val (fpf_x | x) = topenv_get_menuitem_file_close ()
  val () = gtk_widget_set_sensitive (x, GTRUE)
  prval () = fpf_x (x)
  val (fpf_x | x) = topenv_get_menuitem_file_save ()
  val () = gtk_widget_set_sensitive (x, GTRUE)
  prval () = fpf_x (x)
  val (fpf_x | x) = topenv_get_menuitem_file_saveas ()
  val () = gtk_widget_set_sensitive (x, GTRUE)
  prval () = fpf_x (x)
//
  val (fpf_x | x) = topenv_get_menuitem_view_fontsel ()
  val () = gtk_widget_set_sensitive (x, GTRUE)
  prval () = fpf_x (x)
  val (fpf_x | x) = topenv_get_menuitem_view_linenumber ()
  val () = gtk_widget_set_sensitive (x, GTRUE)
  prval () = fpf_x (x)
//
  val () = the_drawarea_welcome_fini ()
  val (fpf_container | container) = topenv_get_container_source ()
  val () = gtk_container_add (container, win)
  val () = gtk_widget_show_unref (win)
  prval () = fpf_container (container)
in
  // nothing
end // end of [if]
//
end // end of [topenv_textview_source_initset_if]

(* ****** ****** *)

(* end of [atsui_textview_source.dats] *)
