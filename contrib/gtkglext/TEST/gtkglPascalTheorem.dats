(*
**
** A gtkglext example
** for demonstrating the elegant theorem of Pascal
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2011 // adapted to gtkglext-1.0
**
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "libc/SATS/random.sats"
macdef PI = M_PI
macdef _2PI = 2 * M_PI

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glu.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

typedef dbl = double

// y = k1 * x + b1
// y = k2 * x + b2

fun line_intersect (
    k1: dbl, b1: dbl, k2: dbl, b2: dbl
  ) : @(dbl, dbl) = (x, y) where {
  val x = (b1 - b2) / (k2 - k1); val y = k1 * x + b1
} // end of [line_intersect]

(* ****** ****** *)

fun sort {n:nat}
  (xs: list_vt (double, n)): list_vt (double, n) = let
  var !p_cmp = @lam (x1: &double, x2: &double): Sgn =<clo> compare (x1, x2)
in
  list_vt_mergesort<double> (xs, !p_cmp)
end // end of [sort]

(* ****** ****** *)

fun draw_colinear {l:agz} (
  cr: !cairo_ref l
, x1: double, y1: double, x2: double, y2: double, x3: double, y3: double
) : void =
  if x1 <= x2 then
    if x1 <= x3 then let
      val () = cairo_move_to (cr, x1, y1)
    in
      if x2 <= x3 then cairo_line_to (cr, x3, y3) else cairo_line_to (cr, x2, y2)
    end else let
      val () = cairo_move_to (cr, x3, y3)
    in
      cairo_line_to (cr, x2, y2)
    end
  else // x2 < x1
    if x2 <= x3 then let
      val () = cairo_move_to (cr, x2, y2)
    in
      if x1 <= x3 then cairo_line_to (cr, x3, y3) else cairo_line_to (cr, x1, y1)
    end else let
      val () = cairo_move_to (cr, x3, y3)
    in
      cairo_line_to (cr, x1, y1)
    end 
  // end of [if]
(* end of [draw_colinear] *)

(* ****** ****** *)

#define :: list0_cons
#define nil list0_nil

fun genRandDoubles
  {n:nat} (n: int n): list_vt (double, n) =
  if n > 0 then let
    val x = drand48 () in list_vt_cons (x, genRandDoubles (n-1))
  end else list_vt_nil
// end of [genRandDoubles]

local
//
// nothing
//
in // in of [local]
//
val theVertices
  : ref (list0 double) = let
  val ts = genRandDoubles (6)
  val ts = sort (ts); val ts = list0_of_list_vt (ts)
in
  ref_make_elt<list0 double> (ts)
end // enbd of [theVertices]
val theVerticesLst
  : ref (list0 (list0 double)) = ref (list0_nil)
// end of [theVerticesLst]
//
fun theVerticesLst_push () = let
  val ts = genRandDoubles (6)
  val ts = sort (ts); val ts = list0_of_list_vt (ts)
  val () = !theVerticesLst := list0_cons (!theVertices, !theVerticesLst)
in
  !theVertices := ts
end // end of [theVerticesLst_push]
//
fun theVerticesLst_pop () =
  case+ !theVerticesLst of
  | list0_cons (x, xs) => (!theVerticesLst := xs; !theVertices := x)
  | list0_nil () => ()
// end of [theVerticesLst_pop]
//
end // end of [local]

(* ****** ****** *)

extern
fun drawPascalTheorem {l:agz} (
  cr: !cairo_ref l, W: double, H: double, ts: list0 (double)
) : void // end of [drawPascalTheorem]

implement
drawPascalTheorem
  (cr, W, H, ts) = () where {
  val- t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: nil () = ts
  val a1 = _2PI * t1
  val x1 = cos a1 and y1 = sin a1
  val a2 = _2PI * t2
  val x2 = cos a2 and y2 = sin a2
  val a3 = _2PI * t3
  val x3 = cos a3 and y3 = sin a3
  val a4 = _2PI * t4
  val x4 = cos a4 and y4 = sin a4
  val a5 = _2PI * t5
  val x5 = cos a5 and y5 = sin a5
  val a6 = _2PI * t6
  val x6 = cos a6 and y6 = sin a6
//
  val k12 = (y1 - y2) / (x1 - x2)
  val b12 = y1 - k12 * x1
  val k23 = (y2 - y3) / (x2 - x3)
  val b23 = y2 - k23 * x2
  val k34 = (y3 - y4) / (x3 - x4)
  val b34 = y3 - k34 * x3
  val k45 = (y4 - y5) / (x4 - x5)
  val b45 = y4 - k45 * x4
  val k56 = (y5 - y6) / (x5 - x6)
  val b56 = y5 - k56 * x5
  val k61 = (y6 - y1) / (x6 - x1)
  val b61 = y6 - k61 * x6
//
  val (px1, py1) = line_intersect (k12, b12, k45, b45)
  val (px2, py2) = line_intersect (k23, b23, k56, b56)
  val (px3, py3) = line_intersect (k34, b34, k61, b61)
//
  val pxs = let
    #define nil list_vt_nil
    #define :: list_vt_cons
  in
    1.0 :: ~1.0 :: px1 :: px2 :: px3 :: nil ()
  end // end of [val]
  val qxs = sort (pxs)
  val ~list_vt_cons (qx1, qxs) = qxs
  val ~list_vt_cons (_qx2, qxs) = qxs
  val ~list_vt_cons (_qx3, qxs) = qxs
  val ~list_vt_cons (_qx4, qxs) = qxs
  val ~list_vt_cons (qx5, qxs) = qxs
  val ~list_vt_nil () = qxs
//
  val dx = qx5 - qx1
//
  val pys = let
    #define nil list_vt_nil
    #define :: list_vt_cons
  in
    1.0 :: ~1.0 :: py1 :: py2 :: py3 :: nil ()
  end // end of [val]
  val qys = sort (pys)
  val ~list_vt_cons (qy1, qys) = qys
  val ~list_vt_cons (_qy2, qys) = qys
  val ~list_vt_cons (_qy3, qys) = qys
  val ~list_vt_cons (_qy4, qys) = qys
  val ~list_vt_cons (qy5, qys) = qys
  val ~list_vt_nil () = qys
//
  val dy = qy5 - qy1
//
  val WH = min (W, H)
  val dxy = max (dx, dy)
  val alpha = WH / dxy
//
  val () = cairo_translate (cr, (W-WH)/2, (H-WH)/2)
//
  val () = cairo_scale (cr, alpha, alpha)
  val () = cairo_rectangle (cr, 0.0, 0.0, dxy, dxy)
  val () = cairo_set_source_rgb (cr, 1.0, 1.0, 1.0) // white color
  val () = cairo_fill (cr)
//
  val () = cairo_translate (
    cr, (dxy - dx) / 2 - (qx1/dx)*dx, (dxy - dy) / 2 - (qy1/dy)*dy
  ) // end of [val]
//
  val xc = 0.0 and yc = 0.0; val rad = 1.0
  val () = cairo_arc (cr, xc, yc, rad, 0.0, _2PI)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 1.0) // blue color
  val () = cairo_fill (cr)
//
  val () = cairo_move_to (cr, x1, y1)
  val () = cairo_line_to (cr, x2, y2)
  val () = cairo_line_to (cr, x3, y3)
  val () = cairo_line_to (cr, x4, y4)
  val () = cairo_line_to (cr, x5, y5)
  val () = cairo_line_to (cr, x6, y6)
  val () = cairo_close_path (cr)
  val () = cairo_set_source_rgb (cr, 1.0, 1.0, 0.0) // yellow color
  val () = cairo_fill (cr)
//
  val () = cairo_set_line_width (cr, 0.01)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0) // black color
//
  val () = draw_colinear (cr, x1, y1, x2, y2, px1, py1)
  val () = draw_colinear (cr, x4, y4, x5, y5, px1, py1)
//
  val () = draw_colinear (cr, x2, y2, x3, y3, px2, py2)
  val () = draw_colinear (cr, x5, y5, x6, y6, px2, py2)
//
  val () = draw_colinear (cr, x3, y3, x4, y4, px3, py3)
  val () = draw_colinear (cr, x6, y6, x1, y1, px3, py3)
//
  val () = draw_colinear (cr, px1, py1, px2, py2, px3, py3)
//
  val () = cairo_stroke (cr)
//
} // end of [drawPascalTheorem]

(* ****** ****** *)

staload
"contrib/atspslide/SATS/atspslide.sats"
dynload "contrib/atspslide/dynloadall.dats"

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
fun initialize (): void = "initialize"
implement initialize () = let
(*
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
*)
  val () = glClearColor (0.5, 0.5, 0.5, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val ratio = 0.725
(*
  val () = glOrtho (~1.0*ratio, 1.0*ratio, ~1.0*ratio, 1.0*ratio, 1.0, 10.0)
*)
  val () = glFrustum (~1.0*ratio, 1.0*ratio, ~1.0*ratio, 1.0*ratio, 9.0, 12.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
  val () = gluLookAt (0.0, 0.0, 10.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
in
  // empty
end // end of [initialize]

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
//
    val () = glViewport ((w-wh)/2, (h-wh)/2, wh, wh)
//
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

val theDelta = 5.0
val theAlpha_ref = ref<double> (0.0)
val theRotateknd_ref = ref_make_elt<int> (0)

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
    and height = (int_of)alloc.height
    val WH = min (width, height)
//
(*
    val () = println! ("fexpose: width = ", width)
    val () = println! ("fexpose: height = ", height)
*)
//
    val surface =
      cairo_image_surface_create (CAIRO_FORMAT_ARGB32, WH, WH)
    val width = (double_of)width
    and height = (double_of)height
    val WH = (double_of)WH
//
    val WH1 = WH * 0.9925
    val [l:addr] cr = cairo_create (surface)
//
    val (pf_save | ()) = cairo_save (cr)
    val () = cairo_rectangle (cr, 0.0, 0.0, WH, WH)
    val () = cairo_set_source_rgb (cr, 1.0, 0.0, 0.0) // red color
    val () = cairo_fill (cr)
    val () = (case+ !theVerticesLst of
      | list0_cons (ts, _) => let
          val () = cairo_translate (cr, (WH-WH1)/2, (WH-WH1)/2)
        in
          drawPascalTheorem (cr, WH1, WH1, ts) // previous example
        end // end of [list0_cons]
      | list0_nil () => ()
    ) // end of [val]
    val gltext1 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
    val () = cairo_restore (pf_save | cr)
//
    val (pf_save | ()) = cairo_save (cr)
    val () = cairo_translate (cr, (WH-WH1)/2, (WH-WH1)/2)
    val () = drawPascalTheorem (cr, WH1, WH1, !theVertices)
    val gltext2 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
    val () = cairo_restore (pf_save | cr)
//
    val () = cairo_destroy (cr)
    val () = cairo_surface_destroy (surface)
//
    val () = glClear (GL_COLOR_BUFFER_BIT)
    val () = glColor3d (0.0, 0.0, 0.0) // black color
//
    val knd12 = !theRotateknd_ref; val knd16 = 1 - knd12
//
    val (pfmat | ()) = glPushMatrix ()
    val () = () where {
      val alpha = !theAlpha_ref
      val () = if knd12 > 0 then glRotated (~alpha, 0.0, 1.0, 0.0)
      val () = if knd16 > 0 then glRotated (~alpha, 1.0, 0.0, 0.0)
    } // end of [val]
    val () = glTranslated (~0.5, ~0.5, 0.5)
//
    val () = glEnable (GL_CULL_FACE)
    val () = glCullFace (GL_BACK) // HX: prevent transparency!
    val () = if knd12 > 0 then
      glTexture_mapout_cube12 (gltext1, gltext2, 1.0, 1.0, 1(*down*))
    val () = if knd16 > 0 then
      glTexture_mapout_cube16 (gltext1, gltext2, 1.0, 1.0, 1(*down*))
    val () = glDisable (GL_CULL_FACE)
//
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
#define TIMEOUT_INTERVAL 40
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
      val () = !theRotateknd_ref := randint (2)
      val () = timeout_remove ()
      val () = theVerticesLst_push ()
    in
      !theAlpha_ref := 0.0
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
fun fprev (): void
implement fprev () = let
  val () = theVerticesLst_pop ()
//
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
end // end of [fprev]

(* ****** ****** *)

extern
fun fnext (): void
implement
fnext () = let
//
  val x = !rotate_ref
  val () = !rotate_ref := 1 - x
//
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
end // end of [fnext]

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

macdef gs = gstring_of_string

extern
fun main1 (): void = "main1"
implement
main1 () = () where {
//
val () = srand48_with_time ()
//
val glconfig = gdk_gl_config_new_by_mode (
  GDK_GL_MODE_RGB lor GDK_GL_MODE_ALPHA lor GDK_GL_MODE_DEPTH lor GDK_GL_MODE_DOUBLE
) // end of [glconfig]
//
val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
val () = gtk_window_set_default_size (window, (gint)400, (gint)400)
val (fpf_x | x) = (gs)"gtkglPascalTheorem"
val () = gtk_window_set_title (window, x)
prval () = fpf_x (x)
val _sid = g_signal_connect
(window, (gsignal)"delete_event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
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
//
val (fpf_x | x) = (gs)"_Close"
val btn_close = gtk_button_new_with_mnemonic (x)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (btn_close, (gsignal)"clicked", G_CALLBACK(gtk_main_quit), (gpointer_vt)window)
// end of [val]
val () = gtk_box_pack_end (hbox1, btn_close, GTRUE, GTRUE, (guint)10)
val () = gtk_widget_show_unref (btn_close)
val (fpf_x | x) = (gs)"_Next"
val btn_next = gtk_button_new_with_mnemonic (x)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (btn_next, (gsignal)"clicked", G_CALLBACK(fnext), (gpointer)null)
val () = gtk_box_pack_end (hbox1, btn_next, GTRUE, GTRUE, (guint)10)
val () = gtk_widget_show_unref (btn_next)
val (fpf_x | x) = (gs)"_Prev"
val btn_prev = gtk_button_new_with_mnemonic (x)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (btn_prev, (gsignal)"clicked", G_CALLBACK(fprev), (gpointer)null)
// end of [val]
val () = gtk_box_pack_end (hbox1, btn_prev, GTRUE, GTRUE, (guint)10)
val () = gtk_widget_show_unref (btn_prev)
//
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

(* end of [gtkglPascalTheorem.dats] *)
