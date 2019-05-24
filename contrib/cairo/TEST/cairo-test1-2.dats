(*
**
** A simple CAIRO example: Hello, world!
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(*
** how to compile:
   atscc -o test1 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test1.dats

** how ot test:
   ./test1
   'gthumb' can be used to view the generated image file 'cairo-test1.png'
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libc/SATS/time.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

fun draw_time {l:agz} (
    cr: !cairo_ref l, wd: int, ht: int
  ) : void = let
  // HX: using a fixed-width font
  val () = cairo_select_font_face
    (cr, "Courier", CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD)
  val () = cairo_set_font_size (cr, 32.0)
//
  var time: time_t
  val yn = time_get_and_set (time)
  val () = assert_errmsg (yn, #LOCATION)
  prval () = opt_unsome {time_t} (time)
  var tm: tm_struct
  val _ptr = localtime_r (time, tm)
  val () = assert_errmsg (_ptr > null, #LOCATION)
  prval () = opt_unsome {tm_struct} (tm)
//
  val () = () where {
    var !p_buf with pf_buf = @[byte][32]()
    val _ = strftime (pf_buf | p_buf, 32, "%I:%M:%S %p", tm)
    val (fpf_utf8 | utf8) = strbuf_takeout_ptr (pf_buf | p_buf)
//
    var extents: cairo_text_extents_t
    val () = cairo_text_extents (cr, $UN.castvwtp1{string} (utf8), extents)
    val xc = (wd - extents.width) / 2
(*
    val () = (print "wd = "; print wd; print_newline ())
    val () = (print "xc = "; print xc; print_newline ())
*)
    val yc = (ht - extents.height) / 2
(*
    val () = (print "ht = "; print ht; print_newline ())
    val () = (print "extents.height = "; print extents.height; print_newline ())
    val () = (print "extents.y_bearing = "; print extents.y_bearing; print_newline ())
    val () = (print "yc = "; print yc; print_newline ())
*)
    val () = cairo_move_to (cr, xc - extents.x_bearing, yc - extents.y_bearing)
    val () = cairo_set_source_rgb (cr, 0.0, 0.0, 1.0)
    val () = cairo_show_text (cr, $UN.castvwtp1{string} (utf8))
//
    prval () = fpf_utf8 (utf8)
    prval () = pf_buf := bytes_v_of_strbuf_v (pf_buf)
  } // end of [val]
//
in
  // nothing
end // end of [draw_time]

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

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

%{^
GtkWidget *the_drawingarea = NULL;
ats_ptr_type
the_drawingarea_get () {
  g_object_ref (G_OBJECT(the_drawingarea)); return the_drawingarea ;
}
ats_void_type
the_drawingarea_set (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_drawingarea) g_object_unref (G_OBJECT(the_drawingarea));
  the_drawingarea = x ;
  return ;
} // end of [the_drawingarea_set]
%} // end of [%{^] 
extern fun the_drawingarea_get (): GtkDrawingArea_ref1 = "the_drawingarea_get"
extern fun the_drawingarea_set (x: !GtkDrawingArea_ref1): void = "the_drawingarea_set"

(* ****** ****** *)

fun draw_drawingarea {l:agz}
  (darea: !gobjref (GtkDrawingArea, l)): void = let
  val (fpf_win | win) = gtk_widget_get_window (darea)
in
  if g_object_isnot_null (win) then let
    val cr = gdk_cairo_create (win)
    prval () = minus_addback (fpf_win, win | darea)
    val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
    val () = draw_time (cr, (int_of)p->width, (int_of)p->height)
    prval () = minus_addback (fpf, pf | darea)
    val () = cairo_destroy (cr)
  in
    // nothing
  end else let
    prval () = minus_addback (fpf_win, win | darea)
  in
    // nothing
  end (* end of [if] *)
end // end of [draw_drawingarea]

(* ****** ****** *)

fun fexpose (): gboolean = let
  val darea = the_drawingarea_get ()
  val _ = draw_drawingarea (darea)
  val () = g_object_unref {GtkDrawingArea} (darea)
in
  GFALSE
end // end of [fexpose]

fun ftimeout
  (_: gpointer): gboolean = let
  val darea = the_drawingarea_get ()
  val (fpf_win | win) = gtk_widget_get_window (darea)
in
  if g_object_isnot_null (win) then let
    prval () = minus_addback (fpf_win, win | darea)
    val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
    val () = gtk_widget_queue_draw_area (darea, (gint)0, (gint)0, p->width, p->height)
    prval () = minus_addback (fpf, pf | darea)
    val () = g_object_unref (darea)
  in
    GTRUE
  end else let
    prval () = minus_addback (fpf_win, win | darea)
    val () = g_object_unref (darea)
  in
    GFALSE
  end // end of [if]
end // end of [ftimeout]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_default_size (window, (gint)400, (gint)400)
//
  val (fpf_x | x) = gstring_of_string ("Cairo Digital Clock")
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
//
  val darea = gtk_drawing_area_new ()
  val () = the_drawingarea_set (darea)
  val () = gtk_container_add (window, darea)
  val _sid = g_signal_connect
    (darea, (gsignal)"expose-event", G_CALLBACK (fexpose), (gpointer)null)
  val () = g_object_unref (darea)
  val _sid = g_signal_connect
    (window, (gsignal)"delete-event", G_CALLBACK (gtk_main_quit), (gpointer)null)
  val _sid = g_signal_connect
    (window, (gsignal)"destroy-event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
  val _rid = gtk_timeout_add ((guint32)500U, ftimeout, (gpointer)null)
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

(* end of [cairo-test1-2.dats] *)
