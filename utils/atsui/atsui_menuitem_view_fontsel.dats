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

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/pango/SATS/pango.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"
stadef srcwin = $SWL.srcwin

(* ****** ****** *)

staload "atsui_topenv.sats"
macdef gs = gstring_of_string
overload gint with gint_of_GtkResponseType

(* ****** ****** *)

macdef GNULL = (gpointer)null

(* ****** ****** *)

fun widget_fontsel_by_name
  {c:cls | c <= GtkWidget} {l,l1:agz} (
    widget: !gobjref (c, l), name: !gstring l1
  ) : void = () where {
  val fd = pango_font_description_from_string (name)
  val () = gtk_widget_modify_font (widget, fd)
  val () = pango_font_description_free (fd)
} // end of [widget_fontsel_by_name]

fun widget_get_font_name
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l)): gstring1 = let
  val (fpf_sty | sty) = gtk_widget_get_style (widget)
  val () = assert_errmsg (ptr_of(sty) > null, #LOCATION) // HX: necessary?
  val (fpf_fd | fd) = gtk_style_get_font_desc (sty)
  val () = assert_errmsg (ptr_of(fd) > null, #LOCATION) // HX: necessary?
  val name = pango_font_description_to_string (fd)
  prval () = minus_addback (fpf_fd, fd | sty)
  prval () = minus_addback (fpf_sty, sty | widget)
in
  name
end // end of [widget_get_font_name]

(* ****** ****** *)

fun fontsel_get_font_name_by_selector
  {c:cls | c <= GtkWindow} {l,l1:agz} (
    parent: !gobjref (c, l), fontname0: !gstring l1
  ) : gstring0 = let
  val (fpf_x | x) = (gs)"ATSUI: Font Selection"
  val dialog = gtk_font_selection_dialog_new (x)
  prval () = fpf_x (x)
  val () = gtk_window_set_transient_for (dialog, parent)
  val _gb = gtk_font_selection_dialog_set_font_name (dialog, fontname0)
  val () = (print "fontsel_get_font_name_by_selector: _gb = "; print ((bool_of)_gb); print_newline ())
  val response = gtk_dialog_run (dialog)
  val fontname1 = (
    if response = (gint)GTK_RESPONSE_OK then
      gtk_font_selection_dialog_get_font_name (dialog)
    else gstring_make_null (null)
  ) : gstring0
  val () = gtk_widget_destroy0 (dialog)
in
  fontname1
end // end of [fontsel_get_font_name_by_selector]

fun fontsel_change_font_by_selector
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l)): void = () where {
  val fontname0 = widget_get_font_name (widget)
  val [c1:cls,l1:addr]
    (fpf_topwin | topwin) = gtk_widget_get_toplevel (widget)
  prval () = clstrans {c1,GtkWidget,GObject} ()
  val () = assert_errmsg (GTK_IS_WINDOW (topwin), #LOCATION)
  val fontname1 = fontsel_get_font_name_by_selector (topwin, fontname0)
  prval () = fpf_topwin (topwin)
  val () = (
    print "fontsel_change_font_by_selector: fontname0 = "; print (__cast fontname0); print_newline ();
    print "fontsel_change_font_by_selector: fontname1 = "; print (__cast fontname1); print_newline ();
  ) where {
    extern castfn __cast {l:addr} (x: !gstring l): string
  }
  val p_fontname1 = ptr_of (fontname1)
  val () = if p_fontname1 > null then let
    val () = widget_fontsel_by_name (widget, fontname1)
    // val () = indent_refresh_tab_width (widget)
  in
    // nothing
  end // end of [val]
  val () = gstring_free (fontname0)
  val () = gstring_free (fontname1)
} // end of [fontsel_change_font_by_selector]

(* ****** ****** *)

implement
cb_view_fontsel_activate
  () = GTRUE where {
  val (fpf_tv | tv) =
    topenv_get_textview_source ()
  val () = fontsel_change_font_by_selector (tv)
  prval () = fpf_tv (tv)
} // end of [cb_view_fontsel_activate]
   
(* ****** ****** *)

(* end of [atsui_menuitem_view_fontsel.dats] *)
