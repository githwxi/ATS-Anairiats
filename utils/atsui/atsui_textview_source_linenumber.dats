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
staload _(*anon*) = "contrib/glib/DATS/glib.dats"

(* ****** ****** *)

staload "contrib/pango/SATS/pango.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"

(* ****** ****** *)

macdef gs = gstring_of_string

(* ****** ****** *)

macdef LINENUMBER_MARGIN = 2

fun linenumber_width_eval
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l)): int = width where {
  #define NCOL 4
  val x = g_strnfill ((gsize)NCOL, (gchar)'0')
  val layout = gtk_widget_create_pango_layout (widget, x)
  val () = gstring_free (x)
  var width: int and height: int
  val () = pango_layout_get_pixel_size(layout, width, height);
  val () = g_object_unref (layout)
} // end of [linenumber_width_eval]

(* ****** ****** *)

fun linenumber_get_info
  {c:cls | c <= GtkTextView}
  {l,l1,l2:agz} (
    tv: !gobjref (c, l)
  , y1: gint, y2: gint
  , coords: !GArray_ref (gint, l1)
  , numbrs: !GArray_ref (gint, l2)
  , cntres: &gint? >> gint
  ) : void = () where {
  val () = g_array_set_size (coords, (guint)0)
  val () = g_array_set_size (numbrs, (guint)0)  
//
  var iter: GtkTextIter
  var linetop: gint
  val () = gtk_text_view_get_line_at_y (tv, iter, y1, linetop)
//
  var count: int = 0
  val () = while (true) let
    val is_end = gtk_text_iter_is_end (iter)
    val () = if (bool_of)is_end then break
    var y: gint and height: gint
    val () = gtk_text_view_get_line_yrange (tv, iter, y, height)
    val () = g_array_append_val {gint} (coords, y)
    var linenum = gtk_text_iter_get_line (iter)
    val () = g_array_append_val {gint} (numbrs, linenum)
    val () = count := count + 1
    val () = if (y + height) >= y2 then break
    val () = gtk_text_iter_forward_line (iter)
  in
    // nothing
  end // end of [val]
//
  val () = cntres := (gint)count
} // end of [linenumber_get_info]

(* ****** ****** *)

implement
cb_textview_source_expose_event_linenumber
  {c} (tv, event) = GFALSE where {
  prval () = clstrans {c,GtkTextView,GtkWidget} ()
  val () =
while (true) let
  val (fpf_win | win) = gtk_text_view_get_window (tv, GTK_TEXT_WINDOW_LEFT)
  val p_win = ptr_of (win)
  prval () = minus_addback (fpf_win, win | tv)
  val () = if (event.window <> p_win) then break
//
  val wy1 = event.area.y
  var bx1: gint and by1: gint
  val () = gtk_text_view_window_to_buffer_coords
    (tv, GTK_TEXT_WINDOW_LEFT, (gint)0, wy1, bx1, by1)
  val wy2 = wy1 + event.area.height;
  var bx2: gint and by2: gint      
  val () = gtk_text_view_window_to_buffer_coords
    (tv, GTK_TEXT_WINDOW_LEFT, (gint)0, wy2, bx2, by2)
//
  val coords = g_array_new {gint} (GFALSE, GFALSE, sizeof<gint>)
  val numbrs = g_array_new {gint} (GFALSE, GFALSE, sizeof<gint>)
  var count: gint
  val () = linenumber_get_info (tv, by1, by2, coords, numbrs, count)
  val () = if (count = (gint)0) then let
    val () = count := (gint)1
    var y: gint = (gint)0 and n: gint= (gint)0
    val () = g_array_append_val (coords, y)
    val () = g_array_append_val (numbrs, n)
  in end // end of [val]
//
  val (fpf_x | x) = (gs)""
  val layout = gtk_widget_create_pango_layout (tv, x)
  prval () = fpf_x (x)
//
  val linenumber_width = linenumber_width_eval (tv)
//
  val () = pango_layout_set_width (layout, linenumber_width)
  val () = pango_layout_set_alignment (layout, PANGO_ALIGN_RIGHT)
//
// HX-2010-05-24: this does not work in GTK-2.10
//
  val alist = pango_attr_list_new ()
//
  val (fpf_sty | sty) = gtk_widget_get_style (tv)
  val () = assert_errmsg (ptr_of(sty) > null, ": " + #LOCATION)
  val (fpf_clr, pf_clr | p_clr) = gtk_style_get_text_aa (sty)
  prval (pf1_clr, pf2_clr) = array_v_uncons {GdkColor} (pf_clr)
  val attr = pango_attr_foreground_new (p_clr->red, p_clr->green, p_clr->blue)
  prval () = pf_clr := array_v_cons (pf1_clr, pf2_clr)
  prval () = minus_addback (fpf_clr, pf_clr | sty)
  prval () = minus_addback (fpf_sty, sty | tv)
//
  val () = pango_attr_list_insert (alist, attr)
  val () = pango_layout_set_attributes (layout, alist)
  val () = pango_attr_list_unref (alist)
//
  #define BUFSZ 8
  var !p_buf with pf_buf = @[byte?][BUFSZ]()
//
  var i: gint
  val () = for* {i:nat} (i: gint i) =>
    (i := (gint)0; i < count; i := i + (gint)1) let
    val bx = (gint)0
    val by = g_array_get_elt_at<gint> (coords, i)
    var wx: gint and wy: gint
    val () = gtk_text_view_buffer_to_window_coords (tv, GTK_TEXT_WINDOW_LEFT, bx, by, wx, wy)
(*
    val () = (print "cb_textview_source_expose_event_linenumber: wx = "; print (int_of(wx)); print_newline ())
    val () = (print "cb_textview_source_expose_event_linenumber: wy = "; print (int_of(wy)); print_newline ())
*)
    val n = g_array_get_elt_at<gint> (numbrs, i)
    val n = (int_of)n
    val n = (n + 1)
    val (pf_str, fpf_str | _ntot) = g_snprintf (pf_buf | p_buf, (gulong)BUFSZ, "%4.4d", @(n))
    val str = gstring_of_viewptr (pf_str | p_buf)
    val () = pango_layout_setall_text (layout, str)
    prval () = pf_buf := fpf_str (str)
    val (fpf_sty | sty) = gtk_widget_get_style (tv)
    val () = paint (
      ptr_of(sty)
    , event.window
    , GTK_WIDGET_STATE (tv)
    , GFALSE
    , null
    , (ptr_of)tv
    , null
    , wx-(gint)LINENUMBER_MARGIN
    , wy-(gint)LINENUMBER_MARGIN
    , (ptr_of)layout
    ) where {
      extern fun paint (
        _: ptr // style
      , _: ptr // window
      , _: GtkStateType
      , _: gboolean // use_text
      , _: ptr //
      , _: ptr // widget
      , _: ptr //
      , _: gint, _: gint // x, y
      , _: ptr // layout
      ) : void = "mac#gtk_paint_layout"
    } // end of [val]
    prval () = minus_addback (fpf_sty, sty | tv)
  in
    // nothing
  end // end of [val]
//
  val () = g_object_unref (layout)
//
  val () = g_array_free_true (coords)
  val () = g_array_free_true (numbrs)
in
  break
end // end of [while]  
} // end of [linenumber_expose_event]

(* ****** ****** *)

fun toggle_linenumber
  (tf: gboolean) = () where {
  val tf = (bool_of)tf
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val winsz = (
    if tf then linenumber_width_eval (tv) + LINENUMBER_MARGIN else 0
  ) : int // end of [val]
(*
  val () = (print "toggle_linenumber: winsz = "; print winsz; print_newline ())
*)
  val () = gtk_text_view_set_border_window_size (tv, GTK_TEXT_WINDOW_LEFT, (gint)winsz)
  prval () = fpf_tv (tv)
} // end of [toggle_linenumber]

implement
cb_view_linenumber_activate () = GTRUE where {
  val (fpf_item | item) = topenv_get_menuitem_view_linenumber ()
  val active = gtk_check_menu_item_get_active (item)
  prval () = fpf_item (item)
  val () = toggle_linenumber (active)
} // end of [cb_linenumber_activate]

(* ****** ****** *)

(* end of [atsui_textview_source_linenumber.dats] *)
