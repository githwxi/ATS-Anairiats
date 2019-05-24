(*
**
** A simple CAIRO example: filling rules
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010
**
*)

(*
** how to compile:
   atscc -o test12 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test12.dats

** how ot test:
   ./test12
   'gthumb' can be used to view the generated image file 'cairo-test12.png'
*)

(* ****** ****** *)

staload M = "libc/SATS/math.sats"
macdef PI = $M.M_PI

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

fun draw {l:agz}
  (cr: !cairo_ref l, w: int, h: int): void = () where {
//
  val w = (double_of)w and h = (double_of)h
  val mn = min (w, h)
  val alpha = 1.0*mn / 256
  val () = cairo_translate (cr, (w-mn)/2, (h-mn)/2)
  val () = cairo_scale (cr, alpha, alpha)
//
  val pat = cairo_pattern_create_linear (0.0, 0.0, 0.0, 256.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 1.0, 0.0, 0.0, 0.0, 1.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 0.0, 1.0, 1.0, 1.0, 1.0)
  val () = cairo_set_source (cr, pat)
  val () = cairo_rectangle (cr, 0.0, 0.0, 256.0, 256.0)
  val () = cairo_fill (cr)
  val () = cairo_pattern_destroy (pat)
//
  val pat = cairo_pattern_create_radial (115.2, 102.4, 25.6, 102.4, 102.4, 128.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 1.0, 0.0, 0.0, 0.0, 1.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 0.0, 1.0, 1.0, 1.0, 1.0)
  val () = cairo_set_source (cr, pat)
  val () = cairo_arc (cr, 128.0, 128.0, 76.8, 0.0, 2*PI)
  val () = cairo_fill (cr)
  val () = cairo_pattern_destroy (pat)
} // end of [draw]

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdkclassdec.sats"
staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

fun on_expose_event
  {c:cls | c <= GtkDrawingArea} {l:agz}
  (darea: !gobjref (c, l), event: &GdkEvent): gboolean = let
//
  prval () = clstrans {c,GtkDrawingArea,GtkWidget} ()
//
  val (fpf_win | win) = gtk_widget_get_window (darea)
  val () = assert_errmsg (g_object_isnot_null (win), #LOCATION)
  val cr = gdk_cairo_create (win)
  prval () = minus_addback (fpf_win, win | darea)
  val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
  val () = draw (cr, (int_of)p->width, (int_of)p->height)
  prval () = minus_addback (fpf, pf | darea)
  val () = cairo_destroy (cr)
in
  GFALSE // HX: allowing the signal to be propagated further?
end // end of [on_expose_event]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_default_size (window, (gint)400, (gint)400)
  val (fpf_x | x) =
    (gstring_of_string)"cairo: radial gradients"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
  val darea = gtk_drawing_area_new ()
  val () = gtk_container_add (window, darea)
  val _sid = g_signal_connect
    (darea, (gsignal)"expose-event", G_CALLBACK (on_expose_event), (gpointer)null)
  val () = g_object_unref (darea)
  val _sid = g_signal_connect
    (window, (gsignal)"delete-event", G_CALLBACK (gtk_main_quit), (gpointer)null)
  val _sid = g_signal_connect
    (window, (gsignal)"destroy-event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
  val () = gtk_widget_show_all (window)
  val () = g_object_unref (window) // ref-count becomes 1!
  val () = gtk_main ()
} // end of [val]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$
ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  gtk_init ((int*)&argc, (char***)&argv) ;
  main1 () ;
  return ;
} // end of [mainats]
%} // end of [%{^]

(* ****** ****** *)

(* end of [cairo-test12.dats] *)
