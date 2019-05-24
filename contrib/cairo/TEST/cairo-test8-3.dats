(*
**
** A simple CAIRO example: an illusion of circular motion
** see Kitaoka's page: http://www.ritsumei.ac.jp/~akitaoka/
**
** This is a variant of cairo-test8-1
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010
**
*)

(*
** how to compile:
   atscc -o test8-3 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test8-3.dats

** how ot test:
   ./test8-3
*)

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

#define PI M_PI

(* ****** ****** *)

stadef dbl = double
stadef cr (l:addr) = cairo_ref l

(* ****** ****** *)

fn bw_set {l:agz}
  (cr: !cr l, bw: int): void =
  if bw > 0 then
    cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  else
    cairo_set_source_rgb (cr, 1.0, 1.0, 1.0)
  // end of [if]
// end of [rb_set]

fn rb_set {l:agz}
  (cr: !cr l, rb: int): void =
  if rb > 0 then
    cairo_set_source_rgb (cr, 1.0, 0.75, 0.0)
  else
    cairo_set_source_rgb (cr, 0.0, 0.0, 1.0)
  // end of [if]
// end of [rb_set]

(* ****** ****** *)

fn draw_ring
  {l:agz} {n:int | n >= 2} (
    cr: !cr l
  , bw: int, rb: int
  , rad1: dbl, rad2: dbl
  , n: int n
  ) : void = let
  val alpha =  (1.0 - rad2/rad1) / 1.5
  val delta = 2 * PI / n
//
  fun loop1 {i:nat | i <= n} .<n-i>.
    (cr: !cr l, angle: double, i: int i, bw: int)
    :<cloref1> void = let
    val x2 = rad2 * cos angle
    and y2 = rad2 * sin angle
//
    val angle_nxt = angle + delta
    val () = cairo_move_to (cr, x2, y2)
    val () = cairo_arc (cr, 0., 0., rad1, angle, angle_nxt)
    val () = cairo_arc_negative (cr, 0., 0., rad2, angle_nxt, angle)
    val () = bw_set (cr, bw)
    val () = cairo_fill (cr)
  in
    if i < n then loop1 (cr, angle_nxt, i+1, 1-bw)
  end // end of [loop1]
  val () = loop1 (cr, 0.0, 1, bw)
  fun loop2 {i:nat | i <= n} .<n-i>.
    (cr: !cr l, angle: double, i: int i, rb: int)
    :<cloref1> void = let
    val radm = (rad1 + rad2) / 2
    val drad = rad1 - rad2
    val xm = radm * cos angle
    and ym = radm * sin angle
    val (pf | ()) = cairo_save (cr)
    val () = cairo_translate (cr, xm, ym)
    val () = cairo_rotate (cr, angle)
    // drawing an oval shape:
    val () = cairo_scale (cr, drad/2, drad/3.6)
    val () = cairo_arc (cr, 0., 0., 1., 0., 2*PI)
    val () = cairo_restore (pf | cr)
    val () = rb_set (cr, rb)
    val () = cairo_fill (cr)
  in
    if i < n then loop2 (cr, angle+delta, i+1, 1-rb)
  end // end of [loop2]
  val () = loop2 (cr, 0.0, 1, rb)
in
  // nothing
end // end of [draw_ring]

(* ****** ****** *)

#define SHRINKAGE 0.80
fun draw_rings
  {l:agz} {n:int | n >= 2} (
    cr: !cr l
  , bw: int, rb: int
  , rad_beg: dbl, rad_end: dbl
  , n: int n
  ) : void =
  if rad_beg <= rad_end then let
    val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
    val () = cairo_arc (cr, 0.0, 0.0, rad_beg, 0.0, 2*PI)
    val () = cairo_fill (cr)
  in
    // loop exits
  end else let
    val rad_beg_nxt = SHRINKAGE * rad_beg
    val () = draw_ring (cr, bw, rb, rad_beg, rad_beg_nxt, n)
  in
    draw_rings (cr, 1-bw, 1-rb, rad_beg_nxt, rad_end, n)
  end // end of [if]
// end of [draw_rings]

(* ****** ****** *)

extern fun draw_all {l:agz}
  (cr: !cairo_ref l, width: int, height: int) : void = "draw_main"
implement draw_all
  (cr, wd, ht) = () where {
  val mn = min (wd, ht)
  val xmargin = double_of (wd - mn) / 2
  val ymargin = double_of (ht - mn) / 2
  val (pf0 | ()) = cairo_save (cr)
  val () = cairo_translate (cr, xmargin, ymargin)
  val alpha = 1.0*mn/512
  val wd = 512.0 and ht = 512.0
  val () = cairo_scale (cr, alpha, alpha)
  var i : int = 0 and j : int = 0
  val () = (
    for (i := 0; i < 3; i := i + 1) (
    for (j := 0; j < 3; j := j + 1) let
      val (pf | ()) = cairo_save (cr)
      val () = cairo_translate (cr, i*wd/2, j*ht/2)
      val () = draw_rings (cr, 0, 0, 128.0, 4.0, 40)
      val () = cairo_restore (pf | cr)
    in
      // nothing
    end // end of [for]
    ) // end of [for]
  ) // end of [val]
//
  val () = (
    for (i := 0; i < 2; i := i + 1) (
    for (j := 0; j < 2; j := j + 1) let
      val (pf | ()) = cairo_save (cr)
      val () =
        cairo_translate (cr, i*wd/2+wd/4, j*ht/2+ht/4)
      // end of [val]
      val () = draw_rings (cr, i, 0, 128.0, 4.0, 40)
      val () = cairo_restore (pf | cr)
    in
      // nothing
    end // end of [for]
    ) // end of [for]
  ) // end of [val]
  val () = cairo_restore (pf0 | cr)
} // end of [draw_all]

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
  val () = draw_all (cr, (int_of)p->width, (int_of)p->height)
  prval () = minus_addback (fpf, pf | darea)
  val () = cairo_destroy (cr)
in
  GFALSE // HX: what does this mean?
end // end of [on_expose_event]

(* ****** ****** *)

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_default_size (window, (gint)400, (gint)400)
  val (fpf_x | x) =
    (gstring_of_string)"cairo: Kitaoka's illusory circular motion"
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

(* end of [cairo-test8-3.dats] *)

