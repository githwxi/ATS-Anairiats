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

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "contrib/GL/SATS/gl.sats"

(* ****** ****** *)

val frame_max = 8
val frame_cur_ref = ref_make_elt<int> (0)

val direction_ref = ref_make_elt<int> (1)

val iris_x_ofs_max = 1.5
val hair_move_angle1_max = M_PI / 3
val hair_move_angle2_max = M_PI / 2
val hair_move_angle3_max = 2 * M_PI / 3

val head_rotate_angle_max = 30.0

(* ****** ****** *)

fn draw_arc
  {n:int | n >= 1} (
  radius: double
, ang_init: double, ang_delta: double
, n: int n
) : void = let
  val theta = (ang_delta / n)
  fun loop {i:nat | i <= n}
    (i: int i, theta_i: double):<cloref1> void = let
    val () = glVertex3d
      (radius * cos (theta_i), radius * sin (theta_i), 0.0)
  in
    if i < n then loop (i + 1, theta_i + theta)
  end
  val (pf | ()) = glBegin (GL_LINE_STRIP)
  val () = loop (0, ang_init)
  val () = glEnd (pf | (*none*))
in
  // empty
end // end of [draw_arc]

(* ****** ****** *)

fn draw_polygon_eqlat
  {n:int | n >= 3} (
  knd: GLenum, radius: double, n: int n
) : void = let
  val theta = (2 * M_PI) / n
  fun loop {i:nat | i <= n}
    (i: int i, theta_i: double):<cloref1> void =
    if i < n then let
      val () = glVertex3d
        (radius * cos (theta_i), radius * sin (theta_i), 0.0)
    in
      loop (i + 1, theta_i + theta)
    end
  val (pf | ()) = glBegin (knd)
  val () = loop (0, 0.0)
  val () = glEnd (pf | (*none*))
in
  // empty
end // end of [draw_polygon_eqlat]

(* ****** ****** *)

fn draw_eye (
  width: double
, height: double
, iris_x_ofs: double
) : void = let
  val r = height / 2
  val theta = atan2 (height, width)
  val theta2 = 2 * theta
  val theta4 = 2 * theta2
  val sin_theta = sin (theta)
  val dist = sqrt (height * height + width * width)
  val R2 = dist / (2 * sin_theta)
  val R = R2 / 2

  val (pf_push | ()) = glPushMatrix ()
  val () = glTranslated (0.0, R - r, 0.0)
  val () = draw_arc (R, 1.5 * M_PI - theta2, theta4, 16)
  val () = glPopMatrix (pf_push | (*none*))

  val (pf_push | ()) = glPushMatrix ()
  val () = glTranslated (0.0, r - R, 0.0)
  val () = draw_arc (R, 0.5 * M_PI - theta2, theta4, 16)
  val () = glPopMatrix (pf_push | (*none*))

  val (pf_push | ()) = glPushMatrix ()
  val () = glTranslated (iris_x_ofs, 0.0, 0.0)
  val () = glColor3d (0.0, 0.0, 0.0)
  val () = draw_polygon_eqlat (GL_POLYGON, r / 1.25, 16)

  val () = glColor3d (1.0, 1.0, 1.0)
  val () = glTranslated (iris_x_ofs / 2, 0.0, 0.0)
  val () = draw_polygon_eqlat (GL_POLYGON, r / 8, 16)
  val () = glColor3d (0.0, 0.0, 0.0)
  val () = glPopMatrix (pf_push | (*none*))
in
  // empty
end // end of [draw_eye]

(* ****** ****** *)

fn draw_face (
  face_radius: double, anim_ratio: double, sgn: int
) : void = let
  val hair_length = 4.0
  val hair_angle = M_PI / 3
  val mouth_angle = 0.425 * M_PI

  val (pf_push | ()) = glPushMatrix ()
  val () = glScaled (1.0625, 1.3125, 1.0)

  val () = begin
    if sgn > 0 then begin
      glColor3d (anim_ratio, 0.5, 1.0 - anim_ratio)
    end else begin
      glColor3d (1.0 - anim_ratio, 0.5, anim_ratio)
    end
  end // end of [val]

  val () = draw_polygon_eqlat (GL_POLYGON, face_radius, 64)
  val () = glColor3d (0.0, 0.0, 0.0)
  val (pf_beg | ()) = glBegin (GL_LINES)

  val x_hair = face_radius * cos (hair_angle)
  val y_hair = face_radius * sin (hair_angle)

  val (pf_push1 | ()) = glPushMatrix ()
  val ang1 = (
    if sgn > 0 then
      anim_ratio * hair_move_angle3_max
    else
      anim_ratio * hair_move_angle1_max
  ) : double
  val ang2 = anim_ratio * hair_move_angle2_max
  val ang3 = (
    if sgn > 0 then
      anim_ratio * hair_move_angle1_max
    else
      anim_ratio * hair_move_angle3_max
  ) : double
  val x_delta1 = sgn * hair_length * sin (ang1)
  val y_delta1 = hair_length * cos (ang1)
  val x_delta2 = sgn * hair_length * sin (ang2)
  val y_delta2 = hair_length * cos (ang2)
  val x_delta3 = sgn * hair_length * sin (ang3)
  val y_delta3 = hair_length * cos (ang3)
  val () = glVertex3d (~x_hair, y_hair, 0.0)
  val () = glVertex3d (~x_hair - x_delta1, y_hair + y_delta1, 0.0)
  val () = glVertex3d (0.0, face_radius, 0.0)
  val () = glVertex3d (~x_delta2, face_radius + y_delta2, 0.0)
  val () = glVertex3d (x_hair, y_hair, 0.0)
  val () = glVertex3d (x_hair - x_delta3, y_hair + y_delta3, 0.0)  
  val () = glPopMatrix (pf_push1 | (*none*))
  val () = glEnd (pf_beg | (*none*))
  val () = glPopMatrix (pf_push | (*none*))

  // eye drawing
  val iris_x_ofs = sgn * (anim_ratio * iris_x_ofs_max)
  val (pf_push | ()) = glPushMatrix ()
  val () = glTranslated (~4.0, 4.0, 0.0)
  val () = draw_eye (6.0, 3.0, iris_x_ofs)
  val () = glPopMatrix (pf_push | (*none*))

  val (pf_push | ()) = glPushMatrix ()
  val () = glTranslated (4.0, 4.0, 0.0)
  val () = draw_eye (6.0, 3.0, iris_x_ofs)
  val () = glPopMatrix (pf_push | (*none*))

  // mouth drawing
  val (pf_push | ()) = glPushMatrix ()
  val () =
    if sgn > 0 then let
      val () = glTranslated (0.0, ~4.0, 0.0)
      val () = draw_arc (2.5, 1.5 * M_PI - mouth_angle, 2 * mouth_angle, 32)
    in
      // empty
    end else let
      val () = glTranslated (0.0, ~7.0, 0.0)
      val () = draw_arc (2.5, 0.5 * M_PI - mouth_angle, 2 * mouth_angle, 32)
    in
      // empty
    end // end of [if]
  val () = glPopMatrix (pf_push | (*none*))
in
  // empty
end // end of [draw_face]

(* ****** ****** *)

local

fn glClearColor_white
  (): void = glClearColor (1.0, 1.0, 1.0, 0.0)
// end of [glClearColor_white]

in // in of [local]

extern
fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor_white ()
  val () = glShadeModel (GL_FLAT)
//
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (~25.0, 25.0, ~25.0, 25.0, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
//
in
  // empty
end // end of [initialize]

end // end of [local]

(* ****** ****** *)
//
extern
fun display (): void = "display"
//
implement
display () = let
//
  val face_radius = 10.0
  val frame = !frame_cur_ref
  val anim_ratio = (double_of frame) / frame_max
  val dir = !direction_ref
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glLineWidth (2.5)
  val () = glColor3d (0.0, 0.0, 0.0)
//
  val head_rotate_angle = anim_ratio * head_rotate_angle_max
  val x_ratio = cos (head_rotate_angle * M_PI / 180)
//
  val (pf | ()) = glPushMatrix ()
  val () = glTranslated (~13.75, 0.0, 0.0)
  val () = draw_face (face_radius, anim_ratio, 1)
  val () = glPopMatrix (pf | (*none*))
  val (pf | ()) = glPushMatrix ()
  val () = glTranslated (13.75, 0.0, 0.0)
  val () = draw_face (face_radius, anim_ratio, ~1)
  val () = glPopMatrix (pf | (*none*))
in
  // nothing
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
    val () = glClearColor (1.0, 1.0, 1.0, 1.0)
    val () = glClearDepth ((GLclampd)1.0)
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
(*
  val () = println! ("can_begin = ", can_begin)
*)
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

extern
fun ftimeout (): gboolean = "ftimeout"
implement
ftimeout () = let
  val darea = theDrawingArea_get ()
  val (fpf_win | win) = gtk_widget_get_window (darea)
  val (pf, fpf | p_alloc) = gtk_widget_getref_allocation (darea)
//
  prval pf = GtkAllocation2GdkRectangle (pf)
  val () = gdk_window_invalidate_rect (win, !p_alloc, GFALSE)
  prval pf = GdkRectangle2GtkAllocation (pf)
  prval () = minus_addback (fpf, pf | darea)
//
  val frame = !frame_cur_ref
  val frame_new = begin
    if frame < frame_max then frame + 1 else 0
  end // end of [val]
  val () = if frame_new = 0 then let
    val dir = !direction_ref in !direction_ref := ~dir
  end // end of [val]
  val () = !frame_cur_ref := frame_new
//
  val () = gdk_window_process_updates (win, GFALSE)
  prval () = minus_addback (fpf_win, win | darea)
  val () = g_object_unref (darea)
in
  GTRUE
end // end of [ftimeout]

(* ****** ****** *)

%{$
//
guint timeout_id = 0 ;
//
#define TIMEOUT_INTERVAL 100
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

val toggle_ref = ref_make_elt<int> (0)

extern
fun ftoggle (): void
implement
ftoggle () = let
  val x = !toggle_ref
  val () = !toggle_ref := 1 - x
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
end // end of [ftoggle]

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
val (fpf_x | x) = (gs)"Happy vs Gloomy"
val () = gtk_window_set_title (window, x)
prval () = fpf_x (x)
val _sid = g_signal_connect
(window, (gsignal)"delete-event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
val _sid = g_signal_connect
(window, (gsignal)"destroy", G_CALLBACK (gtk_main_quit), (gpointer)null)
//
val vbox0 = gtk_vbox_new (GFALSE(*homo*), (gint)10(*spacing*))
val () = gtk_container_add (window, vbox0)
//
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

(* end of [gtkglFaces.dats] *)
