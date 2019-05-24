(*
**
** An example of cube rotation involving cairo and texturing
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2011 // adapted to gtkglext-1.0
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

staload
"contrib/atspslide/SATS/atspslide.sats"
dynload "contrib/atspslide/dynloadall.dats"

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
  val () = glOrtho (~1.0, 1.0, ~1.0, 1.0, ~10.0, 10.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
in
  // empty
end // end of [initialize]

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

extern
fun funrealize {l:agz} (
  darea: !GtkDrawingArea_ref l, data: gpointer
) : void = "funrealize"
implement
funrealize (darea, data) = let
(*
  val () = println! ("funrealize: enter")
*)
in 
  // nothing
end // end of [funrealize]

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

val theDelta = 10.0
val theAlpha_ref = ref<double> (0.0)

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
//
    var alloc: GtkAllocation
    val () = gtk_widget_get_allocation (darea, alloc)
    val width = (int_of)alloc.width
    val height = (int_of)alloc.height
//
(*
    val () = println! ("fexpose: width = ", width)
    val () = println! ("fexpose: height = ", height)
*)
//
    val surface =
      cairo_image_surface_create (CAIRO_FORMAT_ARGB32, width, height)
    val width = (double_of)width and height = (double_of)height
//
    val cr = cairo_create (surface)
    val (pf_save | ()) = cairo_save (cr)
    val () = cairo_scale (cr, width, height)
    val () = cairo_rectangle (cr, 0.0, 0.0, 1.0, 1.0)
    val () = cairo_set_source_rgb (cr, 1.0, 0.0, 0.0) // red color
    val () = cairo_fill (cr)
    val gltext1 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
    val () = cairo_restore (pf_save | cr)
//
    val (pf_save | ()) = cairo_save (cr)
    val () = cairo_scale (cr, width, height)
    val () = cairo_rectangle (cr, 0.0, 0.0, 1.0, 1.0)
    val () = cairo_set_source_rgb (cr, 0.0, 0.0, 1.0) // blue color
    val () = cairo_fill (cr)
    val gltext2 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
    val () = cairo_restore (pf_save | cr)
//
    val () = cairo_destroy (cr)
    val () = cairo_surface_destroy (surface)
//
    val () = glClear (GL_COLOR_BUFFER_BIT)
    val () = glColor3d (0.0, 0.0, 0.0) // black color
//
    val (pfmat | ()) = glPushMatrix ()
    val () = let
      val alpha = !theAlpha_ref in glRotated (~alpha, 0.0, 1.0, 0.0)
    end // end of [val]
    val () = glTranslated (~0.5, ~0.5, 0.5)
    val () = glTexture_mapout_cube12 (gltext1, gltext2, 1.0, 1.0, 1(*down*))
    val () = glPopMatrix (pfmat | (*none*))
//
    val () = glDeleteTexture (gltext1)
    val () = glDeleteTexture (gltext2)
//
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

%{$
//
guint timeout_id = 0 ;
//
#define TIMEOUT_INTERVAL 50
//
void timeout_add () {
  if (timeout_id == 0) {
    timeout_id = g_timeout_add (TIMEOUT_INTERVAL, (GSourceFunc)ftimeout, NULL);
  } ; return ;
} // end of [timeout_add]
//
void timeout_remove () {
  if (timeout_id != 0) {
    g_source_remove (timeout_id); timeout_id = 0;
  } ; return ;
} // end of [timeout_remove]
//
%} // end of [%{$]

extern fun timeout_add (): void = "timeout_add"
extern fun timeout_remove (): void = "timeout_remove"

(* ****** ****** *)

val rotate_ref = ref_make_elt<int> (0)

(* ****** ****** *)

extern
fun ftimeout (): gboolean = "ftimeout"
implement
ftimeout () = let
//
  val alpha = !theAlpha_ref + theDelta
  val () =
    if alpha <= 90.0 then
      !theAlpha_ref := alpha
    else let
      val () = !rotate_ref := 0
      val () = timeout_remove () in !theAlpha_ref := 0.0
    end // end of [if]
  // end of [val]
  val darea = theDrawingArea_get ()
  val (fpf_win | win) = gtk_widget_get_window (darea)
  var alloc: GtkAllocation
  val () = gtk_widget_get_allocation (darea, alloc)
  prval pf = GtkAllocation2GdkRectangle (view@ (alloc))
  val () = gdk_window_invalidate_rect (win, alloc, GFALSE)
  prval () = view@ (alloc) := GdkRectangle2GtkAllocation (pf)
  val () = gdk_window_process_updates (win, GFALSE)
  prval () = minus_addback (fpf_win, win | darea)
  val () = g_object_unref (darea)
in
  GTRUE
end // end of [ftimeout]

(* ****** ****** *)

extern
fun frotate (): void
implement
frotate () = let
  val x = !rotate_ref
  val () = !rotate_ref := 1 - x
in
  if (x = 0) then let
    val () = timeout_add () in (*nothing*)
  end else let
    val () = timeout_remove ()
    var alloc: GtkAllocation
    val darea = theDrawingArea_get ()
    val () = gtk_widget_get_allocation (darea, alloc)
    prval pf = GtkAllocation2GdkRectangle (view@ (alloc))
    val (fpf_win | win) = gtk_widget_get_window (darea)
    val () = gdk_window_invalidate_rect (win, alloc, GFALSE)
    prval () = view@ (alloc) := GdkRectangle2GtkAllocation (pf)
    val () = gdk_window_process_updates (win, GFALSE)
    prval () = minus_addback (fpf_win, win | darea)
    val () = g_object_unref (darea)
  in
    // nothing
  end // end of [if]
end // end of [frotate]

(* ****** ****** *)

fun
map_event (): gboolean = let
(*
  val () = println! ("map_event: enter")
*)
  val () = if (!rotate_ref = 1) then timeout_add () in GTRUE
end // end of [map_event]

fun
unmap_event (): gboolean = let
(*
  val () = println! ("unmap_event: enter")
*)
  val () = if (!rotate_ref = 1) then timeout_remove () in GTRUE
end // end of [unmap_event]

fun
visibility_notify_event (
  widget: gpointer, event: &GdkEventVisibility
) : gboolean = let
(*
  val () = println! ("visibility_notify_event: enter")
*)
  val () = if (!rotate_ref = 1) then
    if (event.state = GDK_VISIBILITY_FULLY_OBSCURED) then timeout_remove () else timeout_add ()
  // end of [if]
in
  GTRUE
end // end of [visibility_notify_event]

(* ****** ****** *)

fun cb_ESCAPE_key_press
  {l:agz} (
  win: !GtkWindow_ref (l), event: &GdkEventKey, data: gpointer
) : gboolean = let
  val kv = event.keyval
in
//
case+ 0 of
| _ when kv=(guint)GDK_Escape => let
    val () = g_signal_stop_emission_by_name (win, (gsignal)"key_press_event")
    val () = gtk_widget_destroy (win)
  in
    GTRUE
  end // end of [_ when ...]
| _ => GFALSE
//
end // end of [cb_ESCAPE_key_press]

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
//
val () = gtk_window_set_default_size (window, (gint)400, (gint)400)
val (fpf_x | x) = (gs)"gtkglCubeRot"
val () = gtk_window_set_title (window, x)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (window, (gsignal)"delete_event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
val _sid = g_signal_connect
  (window, (gsignal)"key_press_event", G_CALLBACK (cb_ESCAPE_key_press), (gpointer)null)
val _sid = g_signal_connect
  (window, (gsignal)"destroy", G_CALLBACK (gtk_main_quit), (gpointer)null)
//
val vbox0 = gtk_vbox_new (GFALSE(*homo*), (gint)10(*spacing*))
//
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
  (darea, (gsignal)"configure_event", G_CALLBACK (fconfigure), (gpointer)null)
val _sid = g_signal_connect
  (darea, (gsignal)"expose_event", G_CALLBACK (fexpose), (gpointer)null)
val _sid = g_signal_connect
  (darea, (gsignal)"unrealize", G_CALLBACK (funrealize), (gpointer)null)

val _sig = g_signal_connect
  (darea, (gsignal)"map_event", G_CALLBACK (map_event), (gpointer)null)
val _sig = g_signal_connect
  (darea, (gsignal)"unmap_event", G_CALLBACK (unmap_event), (gpointer)null)
val _sig = g_signal_connect
  (darea, (gsignal)"visibility_notify_event", G_CALLBACK (visibility_notify_event), (gpointer)null)
//
val () = gtk_widget_show_unref (darea)
//
val hsep = gtk_hseparator_new ()
val () = gtk_box_pack_start (vbox0, hsep, GFALSE, GTRUE, (guint)0)
val () = gtk_widget_show_unref (hsep)
//
val hbox1 = gtk_hbox_new (GFALSE(*homo*), (gint)5(*spacing*))
val () = gtk_box_pack_start (vbox0, hbox1, GFALSE, GTRUE, (guint)10)
val (fpf_x | x) = (gs)"_Rotate"
val btn_next = gtk_button_new_with_mnemonic (x)
prval () = fpf_x (x)
val _sid = g_signal_connect
(btn_next, (gsignal)"clicked", G_CALLBACK(frotate), (gpointer)null)
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
val () = gtk_widget_show_unref (window)
//
val () = if !rotate_ref = 1 then timeout_add () // start the clock
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

(* end of [gtkglCubeRot.dats] *)
