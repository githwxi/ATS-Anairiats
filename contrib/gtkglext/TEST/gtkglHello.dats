(*
**
** A simple OpenGL example
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Summer, 2008 // originally done
** Time: October, 2011 // adapted to gtkglext-1.0
**
*)

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement initialize () = let
(*
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
*)
  val () = glClearColor (0.5, 0.5, 0.5, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (0.0, 1.0, 0.0, 1.0, ~1.0, 1.0)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

extern
fun glColor3d_update (): void

extern
fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
(*
  val () = glColor3d (1.0, 1.0, 1.0)
*)
  val () = glColor3d_update ()
//
  val (pf | ()) = glBegin (GL_POLYGON)
  val () = glVertex3d (0.25, 0.25, 0.0)
  val () = glVertex3d (0.75, 0.25, 0.0)
  val () = glVertex3d (0.75, 0.75, 0.0)
  val () = glVertex3d (0.25, 0.75, 0.0)
  val () = glEnd (pf | (*none*))
in
  // empty
end // end of [display]

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"
staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"

(* ****** ****** *)

staload "contrib/gtkglext/SATS/gdk.sats"
staload "contrib/gtkglext/SATS/gtk.sats"

(* ****** ****** *)

%{^
GtkWidget *theDrawingArea = NULL;
ats_ptr_type
theDrawingArea_get () {
  g_object_ref (G_OBJECT(theDrawingArea)); return theDrawingArea ;
} // end of [theDrawingArea_get]
ats_void_type
theDrawingArea_initset (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (theDrawingArea) g_object_unref (G_OBJECT(theDrawingArea));
  theDrawingArea = x ;
  return ;
} // end of [theDrawingArea_initset]
ats_void_type
theDrawingArea_set_gl_capability
  (ats_ptr_type gl_config) {
  gboolean gl_capability ;
  gl_capability = gtk_widget_set_gl_capability
    (theDrawingArea, gl_config, NULL, TRUE, GDK_GL_RGBA_TYPE) ;
  // end of [gl_capability]
  if (!gl_capability) g_assert_not_reached () ;
  return ;
} // end of [theDrawingArea_set_gl_capability]
%} // end of [%{^] 
//
extern
fun theDrawingArea_get (): GtkDrawingArea_ref1 = "theDrawingArea_get"
extern
fun theDrawingArea_initset (x: !GtkDrawingArea_ref1): void = "theDrawingArea_initset"
//
extern
fun theDrawingArea_set_gl_capability {l:addr}
  (glconfig: !GdkGLConfig_ref (l)): void = "theDrawingArea_set_gl_capability"
// end of [theDrawingArea_set_gl_capability]

(* ****** ****** *)

local

staload _(*anon*) = "prelude/DATS/reference.dats"

typedef
dbl3 = @(double, double, double)
val theRGB = ref<dbl3> @(1.0, 0.0, 0.0) // red

in

implement
glColor3d_update () = let
  val (vbox pf | p) = ref_get_view_ptr (theRGB)
in
  $effmask_ref (glColor3d (p->0, p->1, p->2))
end // end of [glColor3d_update]

fun ftoggle (): void = () where {
//
  val () = {
    val (vbox pf | p) = ref_get_view_ptr (theRGB)
    val () = p->0 := 1.0 - p->0 // toggling
    val () = p->2 := 1.0 - p->2 // toggling
  } // end of [val]
//
  val darea = theDrawingArea_get ()
  val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
(*
  val () = fprintf (stderr_ref, "p->width = %i\n", @(int_of(p->width)))
  val () = fprintf (stderr_ref, "p->height = %i\n", @(int_of(p->height)))
*)
  val () = gtk_widget_queue_draw_area (darea, (gint)0, (gint)0, p->width, p->height)
  prval () = minus_addback (fpf, pf | darea)
  val () = g_object_unref (darea)
//
} // end of [ftoggle]

end // end of [local]

(* ****** ****** *)

extern
fun frealize {l:agz} (
  darea: !GtkDrawingArea_ref l, data: gpointer
) : void = "frealize"
implement
frealize (darea, data) = let
  val (fpf1 | glcontext) = gtk_widget_get_gl_context (darea)
  val (fpf2 | gldrawable) = gtk_widget_get_gl_drawable (darea)
  val (pfbeg | can_begin) = gdk_gl_drawable_gl_begin (gldrawable, glcontext)
  prval () = minus_addback (fpf1, glcontext | darea)
in
  if (can_begin) then let
    val () = initialize ()
    val () = gdk_gl_drawable_gl_end (pfbeg | gldrawable)
    prval () = minus_addback (fpf2, gldrawable | darea)
  in
    // nothing
  end else let
    prval () = gdkgl_begin_false_elim (pfbeg)
    prval () = minus_addback (fpf2, gldrawable | darea)
  in
    // nothing
  end // end of [if]
end // end of [frealize]

(* ****** ****** *)

extern
fun fconfigure {l:agz} (
  darea: !GtkDrawingArea_ref l, event: &GdkEvent
) : gboolean = "fconfigure"
implement
fconfigure (darea, event) = let
  val (fpf1 | glcontext) = gtk_widget_get_gl_context (darea)
  val (fpf2 | gldrawable) = gtk_widget_get_gl_drawable (darea)
  val (pfbeg | can_begin) = gdk_gl_drawable_gl_begin (gldrawable, glcontext)
  prval () = minus_addback (fpf1, glcontext | darea)
in
  if (can_begin) then let
    val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
    val () = gtk_widget_queue_draw_area (darea, (gint)0, (gint)0, p->width, p->height)
    val w = (int_of)p->width
    val h = (int_of)p->height
    val wh = min (w, h)
    val () = glViewport ((w-wh)/2, (h-wh)/2, wh, wh)
    prval () = minus_addback (fpf, pf | darea)
    val () = initialize ()
    val () = gdk_gl_drawable_gl_end (pfbeg | gldrawable)
    prval () = minus_addback (fpf2, gldrawable | darea)
  in
    GTRUE
  end else let
    prval () = gdkgl_begin_false_elim (pfbeg)
    prval () = minus_addback (fpf2, gldrawable | darea)
  in
    GFALSE
  end // end of [if]
end (* end of [fconfigure] *)

(* ****** ****** *)

extern
fun fexpose {l:agz} (
  darea: !GtkDrawingArea_ref l, event: &GdkEvent
) : gboolean = "fexpose"

implement
fexpose (darea, event) = let
(*
  val () = println! ("fexpose: enter")
*)
  val (fpf_glcontext | glcontext) = gtk_widget_get_gl_context (darea)
  val (fpf_gldrawable | gldrawable) = gtk_widget_get_gl_drawable (darea)
  val is_double_buffered = gdk_gl_drawable_is_double_buffered (gldrawable)
  val (pfbeg | can_begin) = gdk_gl_drawable_gl_begin (gldrawable, glcontext)
  prval () = minus_addback (fpf_glcontext, glcontext | darea)
in
  if (can_begin) then let
    val () = display ()
    val () = if ((bool_of)is_double_buffered) then
      gdk_gl_drawable_swap_buffers (gldrawable) else glFlush ()
    // end of [if]
    val () = gdk_gl_drawable_gl_end (pfbeg | gldrawable)
    prval () = minus_addback (fpf_gldrawable, gldrawable | darea)
  in
    GTRUE
  end else let
    prval () = gdkgl_begin_false_elim (pfbeg)
    prval () = minus_addback (fpf_gldrawable, gldrawable | darea)
  in
    GFALSE
  end // end of [if]
end // end of [fexpose]

(* ****** ****** *)

macdef gs = gstring_of_string

extern
fun main1 (): void = "main1"
implement main1 () = () where {
//
val glconfig = gdk_gl_config_new_by_mode (
  GDK_GL_MODE_RGB lor GDK_GL_MODE_ALPHA lor GDK_GL_MODE_DEPTH lor GDK_GL_MODE_DOUBLE
) // end of [glconfig]
//
val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
val () = gtk_window_set_default_size (window, (gint)400, (gint)400)
val (fpf_x | x) = (gs)"gtkglHello"
val () = gtk_window_set_title (window, x)
prval () = fpf_x (x)
val _sid = g_signal_connect
(window, (gsignal)"delete-event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
val _sid = g_signal_connect
(window, (gsignal)"destroy", G_CALLBACK (gtk_main_quit), (gpointer)null)
//
val vbox0 = gtk_vbox_new (GFALSE(*homo*), (gint)10(*spacing*))
val () = gtk_container_add (window, vbox0)
val darea = gtk_drawing_area_new ()
//
val () = theDrawingArea_initset (darea)
val () = theDrawingArea_set_gl_capability (glconfig)
val () = g_object_unref (glconfig)
//
val () = gtk_box_pack_start (vbox0, darea, GTRUE, GTRUE, (guint)0)
val _sid = g_signal_connect_after
  (darea, (gsignal)"realize", G_CALLBACK (frealize), (gpointer)null)
val _sid = g_signal_connect
  (darea, (gsignal)"configure-event", G_CALLBACK (fconfigure), (gpointer)null)
val _sid = g_signal_connect
  (darea, (gsignal)"expose-event", G_CALLBACK (fexpose), (gpointer)null)
//
val () = gtk_widget_show_unref (darea)
//
val hsep = gtk_hseparator_new ()
val () = gtk_box_pack_start (vbox0, hsep, GFALSE, GTRUE, (guint)0)
val () = gtk_widget_show_unref (hsep)
//
val hbox1 = gtk_hbox_new (GFALSE(*homo*), (gint)5(*spacing*))
val () = gtk_box_pack_start (vbox0, hbox1, GFALSE, GTRUE, (guint)10)
val (fpf_x | x) = (gs)"_Toggle"
val btn_next = gtk_button_new_with_mnemonic (x)
prval () = fpf_x (x)
val _sid = g_signal_connect
(btn_next, (gsignal)"clicked", G_CALLBACK(ftoggle), (gpointer)null)
// end of [val]
val () = gtk_box_pack_start (hbox1, btn_next, GTRUE, GTRUE, (guint)10)
val () = gtk_widget_show_unref (btn_next)
val (fpf_x | x) = (gs)"_Close"
val btn_close = gtk_button_new_with_mnemonic (x)
prval () = fpf_x (x)
val _sid = g_signal_connect
(btn_close, (gsignal)"clicked", G_CALLBACK(gtk_main_quit), (gpointer_vt)window)
// end of [val]
val () = gtk_box_pack_start (hbox1, btn_close, GTRUE, GTRUE, (guint)10)
val () = gtk_widget_show_unref (btn_close)
val () = gtk_widget_show_unref (hbox1)
//
val () = gtk_widget_show_unref (vbox0)
//
val () = gtk_widget_show_unref (window) // ref-count becomes 1
//
} // end of [main1]

(* ****** ****** *)

%{^
extern
ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]
implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  int gtkglcheck ;
  GdkGLConfig *glconfig ;
//
  gtk_init ((int*)&argc, (char***)&argv) ;
//
  gtkglcheck =
    gtk_gl_init_check ((int*)&argc, (char***)&argv) ;
  // end of [gtkglcheck]
  if (!gtkglcheck) {
    fprintf (stderr, "[gtk_gl_init] failded!\n"); exit (1) ;
  } // end of [if]
//
  main1 () ;
//
  gtk_main () ;
//
  return ; /* deadcode */
} /* end of [mainats] */

%} // end of[%{$]

(* ****** ****** *)

(* end of [gtkglHello.dats] *)
