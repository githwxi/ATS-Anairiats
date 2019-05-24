(*
**
** A tool for presenting slides
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Summer, 2008 // original version based on SDL
** Time: October, 2011 // adapted to gtkglext-1.0
**
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"
staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "libc/SATS/time.sats"
staload "libc/SATS/random.sats"
macdef PI = M_PI
macdef _2PI = 2 * M_PI

(* ****** ****** *)

staload "GL/SATS/gl.sats"
staload "GL/SATS/glu.sats"
staload "cairo/SATS/cairo.sats"

(* ****** ****** *)

staload "glib/SATS/glib.sats"
staload "glib/SATS/glib-object.sats"
staload "GTK/SATS/gdk.sats"
staload "GTK/SATS/gtk.sats"
staload "GTK/SATS/gtkclassdec.sats"

(* ****** ****** *)

staload "gtkglext/SATS/gdk.sats"
staload "gtkglext/SATS/gtk.sats"

(* ****** ****** *)

staload
"atspslide/SATS/atspslide.sats"
dynload "atspslide/dynloadall.dats" // initializing

(* ****** ****** *)

#define theSlideWidth 16
#define theSlideHeight 9
val theSlideAspect = 1.0 * theSlideHeight / theSlideWidth

(* ****** ****** *)

extern
fun myslide_dirname_get (): string = "myslide_dirname_get"

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
fun theDrawingArea_initset
  {l:agz} (x: !GtkDrawingArea_ref l): void = "theDrawingArea_initset"
//
extern
fun theDrawingArea_set_gl_capability {l:addr}
  (glconfig: !GdkGLConfig_ref (l)): void = "theDrawingArea_set_gl_capability"
// end of [theDrawingArea_set_gl_capability]

(* ****** ****** *)

%{^
GtkWidget *theButtonClose = NULL;
ats_ptr_type
theButtonClose_get () {
  g_object_ref (G_OBJECT(theButtonClose)); return theButtonClose ;
} // end of [theButtonClose_get]
ats_void_type
theButtonClose_initset (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (theButtonClose) g_object_unref (G_OBJECT(theButtonClose));
  theButtonClose = x ;
  return ;
} // end of [theButtonClose_initset]
%}
extern
fun theButtonClose_get (): GtkButton_ref1 = "theButtonClose_get"
extern
fun theButtonClose_initset
  {l:agz} (x: !GtkButton_ref l): void = "theButtonClose_initset"
// end of [theButtonClose_initset]

(* ****** ****** *)

%{^
GtkWidget *theButtonPrev = NULL;
ats_ptr_type
theButtonPrev_get () {
  g_object_ref (G_OBJECT(theButtonPrev)); return theButtonPrev ;
} // end of [theButtonPrev_get]
ats_void_type
theButtonPrev_initset (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (theButtonPrev) g_object_unref (G_OBJECT(theButtonPrev));
  theButtonPrev = x ;
  return ;
} // end of [theButtonPrev_initset]
%}
extern
fun theButtonPrev_get (): GtkButton_ref1 = "theButtonPrev_get"
extern
fun theButtonPrev_initset
  {l:agz} (x: !GtkButton_ref l): void = "theButtonPrev_initset"
// end of [theButtonPrev_initset]

(* ****** ****** *)

%{^
GtkWidget *theButtonNext = NULL;
ats_ptr_type
theButtonNext_get () {
  g_object_ref (G_OBJECT(theButtonNext)); return theButtonNext ;
} // end of [theButtonNext_get]
ats_void_type
theButtonNext_initset (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (theButtonNext) g_object_unref (G_OBJECT(theButtonNext));
  theButtonNext = x ;
  return ;
} // end of [theButtonNext_initset]
%}
extern
fun theButtonNext_get (): GtkButton_ref1 = "theButtonNext_get"
extern
fun theButtonNext_initset
  {l:agz} (x: !GtkButton_ref l): void = "theButtonNext_initset"
// end of [theButtonNext_initset]

(* ****** ****** *)

%{^
GtkWidget *theSpinner = NULL;
ats_ptr_type
theSpinner_get () {
  g_object_ref (G_OBJECT(theSpinner)); return theSpinner ;
} // end of [theSpinner_get]
ats_void_type
theSpinner_initset (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (theSpinner) g_object_unref (G_OBJECT(theSpinner));
  theSpinner = x ;
  return ;
} // end of [theSpinner_initset]
%}
extern
fun theSpinner_get (): GtkSpinButton_ref1 = "theSpinner_get"
extern
fun theSpinner_initset
  {l:agz} (x: !GtkSpinButton_ref l): void = "theSpinner_initset"

(* ****** ****** *)

%{^
GtkWidget *theButtonGoto = NULL;
ats_ptr_type
theButtonGoto_get () {
  g_object_ref (G_OBJECT(theButtonGoto)); return theButtonGoto ;
} // end of [theButtonGoto_get]
ats_void_type
theButtonGoto_initset (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (theButtonGoto) g_object_unref (G_OBJECT(theButtonGoto));
  theButtonGoto = x ;
  return ;
} // end of [theButtonGoto_initset]
%}
extern
fun theButtonGoto_get (): GtkButton_ref1 = "theButtonGoto_get"
extern
fun theButtonGoto_initset
  {l:agz} (x: !GtkButton_ref l): void = "theButtonGoto_initset"
// end of [theButtonGoto_initset]

(* ****** ****** *)

local

val theSlideCount_ref = ref_make_elt<int> (0)

in // in of [local]

fun theSlideCount_get (): int = !theSlideCount_ref
fun theSlideCount_set (n: int): void = !theSlideCount_ref := n

fun theSlideCount_inc
  (): void = let
  val n1 = !theSlideCount_ref + 1
  val () = !theSlideCount_ref := n1
  val spinner = theSpinner_get ()
  val () = gtk_spin_button_set_value (spinner, (gdouble)n1)
  val () = g_object_unref (spinner)
in
  // nothing  
end // end of [theSlideCount_inc]

fun theSlideCount_dec
  (): void = let
  val n = !theSlideCount_ref
in
//
if n > 0 then let
  val n1 = n - 1
  val () = !theSlideCount_ref := n1
  val spinner = theSpinner_get ()
  val () = gtk_spin_button_set_value (spinner, (gdouble)n1)
  val () = g_object_unref (spinner)
in
  // nothing
end // end of [if]
//
end // end of [theSlideCount_dec]

end // end of [local]

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement initialize () = let
//
  val () = glClearColor (0.75, 0.75, 0.75, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
//
(*
//
// HX: [r] should be greater than sqrt(2)/2 for [glOrtho]
//
  val r = 1.41422 / 2
  val w = r and h = r
  val () = glOrtho (~1.0*w, 1.0*w, ~1.0*h, 1.0*h, 1.0, 10.0)
*)
  val r = 1.0 / 2 // HX: for [glFrustum]
  val w = r and h = r
  val znear = 2.0; val zfar = znear + 2.0
  val () = glFrustum (~1.0*w, 1.0*w, ~1.0*h, 1.0*h, znear, zfar)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
  val zdelta = 1.0
  val () = gluLookAt (0.0, 0.0, znear+zdelta, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
//
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
//
    val daw = (int_of)p->width
    val dah = (int_of)p->height
    val uw = theSlideWidth
    val uh = theSlideHeight
    val w = 1.0 * daw / uw
    val h = 1.0 * dah / uh
    val wh = min (w, h)
    val vpw = int_of(wh * uw)
    val vph = int_of(wh * uh)
    val () = glViewport ((daw-vpw)/2, (dah-vph)/2, vpw, vph)
    prval () = minus_addback (fpf, pf | darea)
    val () = initialize ()
//
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
fun cairodraw_slide
  {l:agz} (cr: !cairo_ref (l), count: int): void
// end of [cairodraw_slide]

fun
cairodraw_slide_relative
  {l:agz} (
  cr: !cairo_ref (l), count: int
) : void =
  cairodraw_slide (cr, theSlideCount_get () + count)
// end of [cairodraw_slide_relative]

fun
cairodraw_slide_count
  {l:agz} (
  cr: !cairo_ref (l), count: int
) : void = let
  val (pf | ()) = cairo_save (cr)
  val () = cairo_rectangle (cr, 0.0, 0.0, 1.0, 1.0)
  val () = cairo_set_source_rgb (cr, 0.5, 0.5, 0.5) // midgray color
  val () = cairo_fill (cr)
  val () = cairodraw_circnum (cr, count)
  val () = cairo_restore (pf | cr)
in
  // nothing
end // end of [cairodraw_slide_count]

fun
cairodraw_slide_pngfile
  {l:agz} (
  cr: !cairo_ref (l), path: string
) : void = let
  val wsf = 1.0
  val hsf = 1.0
  val img = cairo_image_surface_create_from_png (path)
  val wimg = cairo_image_surface_get_width (img)
  and himg = cairo_image_surface_get_height (img)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_scale (cr, 1.0*wsf/wimg, 1.0*hsf/himg)
  val () = cairo_set_source_surface (cr, img, 0.0, 0.0)
  val () = cairo_paint (cr)
  val () = cairo_restore (pf | cr)
  val () = cairo_surface_destroy (img)
in
  // nothing
end // end of [cairodraw_slide_count]

local

#define PREFIX "myslide"

fun
slidename_get_by_count
  (count: int): strptr1 = let
  val dirname = myslide_dirname_get ()
in
  sprintf ("%s/%s_%i.png", @(dirname, PREFIX, count))
end // end of [slidename_get_by_count]

in // in of [local]

implement
cairodraw_slide
  (cr, count) = let
  val [l:addr] path = slidename_get_by_count (count)
  val path1 = $UN.castvwtp1 {string} {strptr(l)} (path)
  val isexi = test_file_exists (path1)
in
  if isexi then let
    val () = cairodraw_slide_pngfile (cr, path1)
  in
    strptr_free (path)
  end else let
    val () = cairodraw_slide_count (cr, count)
  in
    strptr_free (path)
  end // end of [if]
end // end of [cairodraw_slide]

end // end of [local]

(* ****** ****** *)

#define
ACTpresent 0 // default
#define ACTrectrot 1
#define ACTtriangrot 2
#define ACTcylindrot 3
#define ACTsliding 4 // left-right/top-bottom
#define ACTdisking 5 // disk expanding (and its reversal)
#define ACTfadeout 6 // fading gradually (and its reversal)
#define ACTfolding01 7 // folding and unfolding
#define ACTfolding02 8 // folding and unfolding
#define ACTrandom01 9 // random squares
#define ACTrandom02 10 // random horizontal stripes
#define ACTrandom03 11 // random vertical stripes

local
//
val theActState_ref = ref<int> (ACTpresent)
//
in
//
fun theActState_get () = !theActState_ref
fun theActState_set (act: int): void = !theActState_ref := act
//
end // end of [val]

val theDelta = 10.0
val theAlpha_ref = ref<double> (0.0)
val theRotateknd_ref = ref_make_elt<int> (0)

(* ****** ****** *)
(*
#define CLOCKND 0 // show no second hand
#define CLOCKND 1 // show the second hand
*)
#define CLOCKND 1
//
macdef cairodraw_clock (cr) = cairodraw_clock01 (,(cr), CLOCKND)
//
(* ****** ****** *)

fun fexpose_present
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 0) // current one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (~0.5, ~0.5, 0.5)
  val () = glTexture_mapout_rect_all (gltext, 1.0, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_present]

(* ****** ****** *)

fun fexpose_rectrot
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val knd12 = !theRotateknd_ref; val knd16 = 1 - knd12
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 0) // current one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext1 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 1) // next one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext2 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
  val () = () where {
    val alpha = !theAlpha_ref
    val () = if knd12 > 0 then glRotated (~alpha/2, 0.0, 1.0, 0.0)
    val () = if knd16 > 0 then glRotated (~alpha/2, 1.0, 0.0, 0.0)
  } // end of [val]
  val () = glTranslated (~0.5, ~0.5, 0.5)
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
in
  // nothing
end // end of [fexpose_rectrot]

(* ****** ****** *)

fun fexpose_triangrot
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val vert = !theRotateknd_ref; val hori = 1 - vert
//
  val [l:addr] cr = cairo_create (surface)
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 0) // current one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext1 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 1) // next one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext2 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
//
  val () = glEnable (GL_CULL_FACE)
  val () = glCullFace (GL_BACK) // HX: prevent transparency!
  val z0 = 1.0/3
  val () = () where {
    val alpha = !theAlpha_ref
    val () = if vert > 0 then glRotated (~2*alpha/3, 0.0, 1.0, 0.0)
    val () = if hori > 0 then glRotated (~2*alpha/3, 1.0, 0.0, 0.0)
  } // end of [val]
  val () = glTranslated (~0.5, ~0.5, z0)
  val () = glTexture_mapout_rect_all (gltext1, 1.0, 1.0, 1(*down*))
  val () = if vert > 0 then {
    val () = glTranslated (1.0, 0.0, 0.0)
    val () = glRotated (120.0, 0.0, 1.0, 0.0)
  } // end of [val]
  val () = if hori > 0 then {
    val () = glTranslated (0.0, 1.0/2, ~sqrt(3.0)/2)
    val () = glRotated (120.0, 1.0, 0.0, 0.0)
  } // end of [val]
  val () = glTexture_mapout_rect_all (gltext2, 1.0, 1.0, 1(*down*))
  val () = glDisable (GL_CULL_FACE)
//
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext1)
  val () = glDeleteTexture (gltext2)
//
in
  // nothing
end // end of [fexpose_triangrot]

(* ****** ****** *)

fun fexpose_cylindrot
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val vert = !theRotateknd_ref; val hori = 1 - vert
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 0) // current one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext1 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 1) // next one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext2 = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
//
  val () = glEnable (GL_CULL_FACE)
  val () = glCullFace (GL_BACK) // HX: prevent transparency!
  val () = () where {
    val alpha = !theAlpha_ref
    val () = if vert > 0 then glRotated (~alpha, 0.0, 1.0, 0.0)
    val () = if hori > 0 then glRotated (~alpha, 1.0, 0.0, 0.0)
  } // end of [val]
  val rad = 1/PI
  val () = glTranslated (0.0, 0.0, rad)
  val () = if vert > 0 then
    glTexture_mapout_cylinder_vert (gltext1, 1.0, 1.0, PI, 1(*down*), 32(*nslide*))
  val () = if hori > 0 then
    glTexture_mapout_cylinder_hori (gltext1, 1.0, 1.0, PI, 1(*down*), 32(*nslide*))
  val () = glTranslated (0.0, 0.0, ~2*rad)
  val () = if vert > 0 then {
    val () = glRotated (180.0, 0.0, 1.0, 0.0)
    val ()=  glTexture_mapout_cylinder_vert (gltext2, 1.0, 1.0, PI, 1(*down*), 32(*nslide*))
  } // end of [val]
  val () = if hori > 0 then {
    val () = glRotated (180.0, 1.0, 0.0, 0.0)
    val () = glTexture_mapout_cylinder_hori (gltext2, 1.0, 1.0, PI, 1(*down*), 32(*nslide*))
  } // end of [val]
  val () = glDisable (GL_CULL_FACE)
//
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext1)
  val () = glDeleteTexture (gltext2)
//
in
  // nothing
end // end of [fexpose_cylindrot]

(* ****** ****** *)

fun fexpose_sliding
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val vert = !theRotateknd_ref; val hori = 1 - vert
//
  val alpha = !theAlpha_ref
  var n: int = 0 and ratio: double = 0.0
  val () = () where {
    val () = if alpha >= 90.0 then n := 1
    val () = if alpha < 90.0 then ratio := alpha/90
    val () = if alpha >= 90.0 then ratio := 2-alpha/90
  } // end of [val]
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, n) // 0/1
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
//
  val () = if vert > 0 then
    cairo_rectangle (cr, 0.0, 0.0, ratio, 1.0)
  val () = if hori > 0 then
    cairo_rectangle (cr, 0.0, 0.0, 1.0, ratio)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 1.0)
  val () = cairo_fill (cr)
//
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (~0.5, ~0.5, 0.5)
  val () = glTexture_mapout_rect_all (gltext, 1.0, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_sliding]

(* ****** ****** *)

fun fexpose_disking
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val alpha = !theAlpha_ref
  var n: int = 0 and ratio: double = 0.0
  val () = () where {
    val () = if alpha >= 90.0 then n := 1
    val () = if alpha < 90.0 then ratio := alpha/90
    val () = if alpha >= 90.0 then ratio := 2-alpha/90
  } // end of [val]
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, n) // 0/1
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
//
  val rad = sqrt (2.0)
  val r0 = rad / 20
  val r1 = rad - r0
  val sigma = ratio * ratio
  val () = cairo_arc (cr, 0.5, 0.5, r0 + sigma * r1, 0.0, _2PI)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 1.0)
  val () = cairo_fill (cr)
//
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (~0.5, ~0.5, 0.5)
  val () = glTexture_mapout_rect_all (gltext, 1.0, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_disking]

(* ****** ****** *)

fun fexpose_fadeout
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val alpha = !theAlpha_ref
  var n: int = 0 and ratio: double = 0.0
  val () = () where {
    val () = if alpha >= 90.0 then n := 1
    val () = if alpha < 90.0 then ratio := alpha/90
    val () = if alpha >= 90.0 then ratio := 2-alpha/90
  } // end of [val]
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, n) // 0/1
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
//
  macdef nrt (x) = pow (,(x), 1.0/8)
  val () = cairo_rectangle (cr, 0.0, 0.0, 1.0, 1.0)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, nrt(ratio))
  val () = cairo_fill (cr)
//
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (~0.5, ~0.5, 0.5)
  val () = glTexture_mapout_rect_all (gltext, 1.0, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_fadeout]

(* ****** ****** *)

fun fexpose_folding01
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val alpha = !theAlpha_ref
  var n: int = 0 and ratio: double = 0.0
  val () = () where {
    val () = if alpha >= 90.0 then n := 1
    val () = if alpha < 90.0 then ratio := alpha/90
    val () = if alpha >= 90.0 then ratio := 2-alpha/90
  } // end of [val]
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, n) // 0/1
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val tx = 0.5 * cos (ratio*PI/2)
  val tz = 0.5 * sin (ratio*PI/2)
//
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (~tx, ~0.5, 0.5)
  val () = glRotated (90*ratio, 0.0, 1.0, 0.0)
  val () = glTexture_mapout_rect (gltext, 0.0, 0.0, 0.5, 1.0, 0.5, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (0.0, ~0.5, 0.5-tz)
  val () = glRotated (~90*ratio, 0.0, 1.0, 0.0)
  val () = glTexture_mapout_rect (gltext, 0.5, 0.0, 1.0, 1.0, 0.5, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_folding01]

(* ****** ****** *)

fun fexpose_folding02
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val alpha = !theAlpha_ref
  var n: int = 0 and ratio: double = 0.0
  val () = () where {
    val () = if alpha >= 90.0 then n := 1
    val () = if alpha < 90.0 then ratio := alpha/90
    val () = if alpha >= 90.0 then ratio := 2-alpha/90
  } // end of [val]
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, n) // 0/1
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val tx = 0.5 * cos (ratio*PI/2)
  val tz = 0.5 * sin (ratio*PI/2)
//
  val (pfmat | ()) = glPushMatrix ()
  val () = if n = 0 then {
    val () = glTranslated (~tx, ~0.5, 0.5)
    val () = glRotated (90*ratio, 0.0, 1.0, 0.0)
    val () = glTexture_mapout_rect (gltext, 0.0, 0.0, 0.5, 1.0, 0.5, 1.0, 1(*down*))
  } // end of [val]
  val () = if n = 1 then {
    val () = glTranslated (~tx, ~0.5, 0.5-tz)
    val () = glRotated (~90*ratio, 0.0, 1.0, 0.0)
    val () = glTexture_mapout_rect (gltext, 0.0, 0.0, 0.5, 1.0, 0.5, 1.0, 1(*down*))
  } // end of [val]
  val () = glPopMatrix (pfmat | (*none*))
  val (pfmat | ()) = glPushMatrix ()
  val () = if n = 0 then {
    val () = glTranslated (0.0, ~0.5, 0.5-tz)
    val () = glRotated (~90*ratio, 0.0, 1.0, 0.0)
    val () = glTexture_mapout_rect (gltext, 0.5, 0.0, 1.0, 1.0, 0.5, 1.0, 1(*down*))
  } // end of [val]
  val () = if n = 1 then {
    val () = glTranslated (0.0, ~0.5, 0.5)
    val () = glRotated (90*ratio, 0.0, 1.0, 0.0)
    val () = glTexture_mapout_rect (gltext, 0.5, 0.0, 1.0, 1.0, 0.5, 1.0, 1(*down*))
  } // end of [val]
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_folding02]

(* ****** ****** *)

local

staload "libc/SATS/random.sats"

#define M 20
#define N 20
#define MN %(M * N)
val xs =
  loop (MN, list_vt_nil) where {
  fun loop {n0,n:nat} .<n>. (
    n: int n, res: list_vt (int, n0)
  ) : list_vt (int, n0+n) =
    if n > 0 then
      loop (n-1, list_vt_cons (n-1, res))
    else res
  // end of [loop]
} // end of [val]
val thePosArray = array_make_lst_vt<int> (MN, xs)

fn{a:viewt@ype}
randshuffle {n:nat} (
  A: &(@[a][n]), n: size_t n
) : void = let
//
fun loop
  {n:nat} {l:addr} .<n>. (
  pfarr: !array_v (a, n, l) | p: ptr l, n: size_t n
) : void =
  if n >= 2 then let
    val i = randsize (n)
    val () = if i > 0 then array_ptr_exch (!p, 0, i)
    prval (pf1at, pf2arr) = array_v_uncons {a} (pfarr)
    val () = loop (pf2arr | p+sizeof<a>, n-1)
    prval () = pfarr := array_v_cons {a} (pf1at, pf2arr)
  in
    // nothing
  end else () // end of [if]
//
in
  loop (view@ (A) | &A, n)
end // end of [randshuffle]

fun thePosArray_reshuffle (): void = let
  val (vbox pf | p) = array_get_view_ptr (thePosArray)
in
  $effmask_ref (randshuffle<int> (!p, MN))
end // end of [thePosArray_reshuffle]

val () = thePosArray_reshuffle ()

fun cairodraw_random_squares
  {l:agz}
  {m,n:pos}
  {asz:nat}
  {s0,k:nat | s0+k <= asz} .<k>. (
  cr: !cairo_ref l
, m: int m, n: int n
, A: &(@[int][asz]), s0: int s0, k: int k
) : void =
  if k > 0 then let
    val pos = A.[s0]
    val pos = int1_of_int (pos)
  in
    if pos < 0 then
      cairodraw_random_squares (cr, m, n, A, s0+1, k-1)
    else let
      val pos_m = pos idiv n
    in
      if pos_m >= m then
        cairodraw_random_squares (cr, m, n, A, s0+1, k-1)
      else let
        val pos_n = pos nmod n
        val xu = 1.0/m and yu = 1.0/n
        val x = pos_m*xu and y = pos_n*yu
        val xE = 0.2*xu and yE = 0.2*yu
        val () = cairo_rectangle (cr, x-xE/2, y-yE/2, xu+xE, yu+yE)
(*
        // if you like disks :
        val () = cairo_arc (cr, x+xu/2, y+yu/2, sqrt(xu*xu+yu*yu)/2, 0.0, _2PI)
*)
        val () = cairo_fill (cr)
      in
        cairodraw_random_squares (cr, m, n, A, s0+1, k-1) 
      end // end of [if]
    end // end of [if]
  end else (
    // nothing
  ) // end of [if]
// end of [cairodraw_random_squares]

fun cairodraw_random_hstripes // horizontal stripes
  {l:agz}
  {mn:pos}
  {asz:nat}
  {s0,k:nat | s0+k <= asz} .<k>. (
  cr: !cairo_ref l
, mn: int mn
, A: &(@[int][asz]), s0: int s0, k: int k
) : void =
  if k > 0 then let
    val pos = A.[s0]
    val pos = int1_of_int (pos)
  in
    if pos < 0 then
      cairodraw_random_hstripes (cr, mn, A, s0+1, k-1)
    else if pos >= mn then
      cairodraw_random_hstripes (cr, mn, A, s0+1, k-1)
    else let
      val yu = 1.0/mn
      val y = pos * yu
      val yE = 0.4*yu
      val () = cairo_rectangle (cr, 0.0, y-yE/2, 1.0, yu+yE)
      val () = cairo_fill (cr)
    in
      cairodraw_random_hstripes (cr, mn, A, s0+1, k-1) 
    end // end of [if]
  end else (
    // nothing
  ) // end of [if]
// end of [cairodraw_random_hstripes]

fun cairodraw_random_vstripes // vertical stripes
  {l:agz}
  {mn:pos}
  {asz:nat}
  {s0,k:nat | s0+k <= asz} .<k>. (
  cr: !cairo_ref l
, mn: int mn
, A: &(@[int][asz]), s0: int s0, k: int k
) : void =
  if k > 0 then let
    val pos = A.[s0]
    val pos = int1_of_int (pos)
  in
    if pos < 0 then
      cairodraw_random_vstripes (cr, mn, A, s0+1, k-1)
    else if pos >= mn then
      cairodraw_random_vstripes (cr, mn, A, s0+1, k-1)
    else let
      val xu = 1.0/mn
      val x = pos * xu
      val xE = 0.2*xu
      val () = cairo_rectangle (cr, x-xE/2, 0.0, xu+xE, 1.0)
      val () = cairo_fill (cr)
    in
      cairodraw_random_vstripes (cr, mn, A, s0+1, k-1) 
    end // end of [if]
  end else (
    // nothing
  ) // end of [if]
// end of [cairodraw_random_vstripes]

in // in of [local]

fun fexpose_random01
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val alpha = !theAlpha_ref
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 0) // current one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
//
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 1.0)
  val () = {
    val k = int_of (alpha/180 * MN)
    val k = int1_of_int (k)
    val () = assertloc (0 <= k && k <= MN)
    val (vbox pf | p) = array_get_view_ptr (thePosArray)
    val () = $effmask_ref (cairodraw_random_squares (cr, M, N, !p, 0, k))
  } // end of [val]
  val () = if (alpha >= 179.999) then thePosArray_reshuffle ()
//
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (~0.5, ~0.5, 0.5)
  val () = glTexture_mapout_rect_all (gltext, 1.0, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_random01]

fun fexpose_random02
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val alpha = !theAlpha_ref
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 0) // current one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
//
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 1.0)
  val () = {
    val k = int_of (alpha/180 * MN)
    val k = int1_of_int (k)
    val () = assertloc (0 <= k && k <= MN)
    val (vbox pf | p) = array_get_view_ptr (thePosArray)
    val () = $effmask_ref (cairodraw_random_hstripes (cr, MN, !p, 0, k))
  } // end of [val]
  val () = if (alpha >= 179.999) then thePosArray_reshuffle ()
//
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (~0.5, ~0.5, 0.5)
  val () = glTexture_mapout_rect_all (gltext, 1.0, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_random02]

fun fexpose_random03
  (vpw: int, vph: int): void = let
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, vpw, vph)
  val vpw = (double_of)vpw
  and vph = (double_of)vph
//
  val alpha = !theAlpha_ref
//
  val [l:addr] cr = cairo_create (surface)
//
  val (pf_save | ()) = cairo_save (cr)
  val () = cairo_scale (cr, vpw, vph)
  val () = cairodraw_slide_relative (cr, 0) // current one
  val () = cairodraw_clock (cr) // HX: a translucent clock layover
//
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 1.0)
  val () = {
    val k = int_of (alpha/180 * MN)
    val k = int1_of_int (k)
    val () = assertloc (0 <= k && k <= MN)
    val (vbox pf | p) = array_get_view_ptr (thePosArray)
    val () = $effmask_ref (cairodraw_random_vstripes (cr, MN, !p, 0, k))
  } // end of [val]
  val () = if (alpha >= 179.999) then thePosArray_reshuffle ()
//
  val () = cairo_restore (pf_save | cr)
  val gltext = glTexture_make_cairo_ref (GL_BGRA_format, cr)
//
  val () = cairo_destroy (cr)
  val () = cairo_surface_destroy (surface)
//
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (0.0, 0.0, 0.0) // black color
//
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (~0.5, ~0.5, 0.5)
  val () = glTexture_mapout_rect_all (gltext, 1.0, 1.0, 1(*down*))
  val () = glPopMatrix (pfmat | (*none*))
//
  val () = glDeleteTexture (gltext)
//
in
  // nothing
end // end of [fexpose_random03]

end // end of [local]

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
//
    var alloc: GtkAllocation
    val () = gtk_widget_get_allocation (darea, alloc)
//
    val daw = (int_of)alloc.width
    and dah = (int_of)alloc.height
    val uw = theSlideWidth
    val uh = theSlideHeight
    val w = 1.0 * daw / uw
    val h = 1.0 * dah / uh
    val wh = min (w, h)
    val vpw = int_of(wh * uw)
    val vph = int_of(wh * uh)
//
    val theActState = theActState_get ()
    val () = (
      case+ theActState of
      | ACTrectrot => fexpose_rectrot (vpw, vph)
      | ACTtriangrot => fexpose_triangrot (vpw, vph)
      | ACTcylindrot => fexpose_cylindrot (vpw, vph)
      | ACTsliding => fexpose_sliding (vpw, vph)
      | ACTdisking => fexpose_disking (vpw, vph)
      | ACTfadeout => fexpose_fadeout (vpw, vph)
      | ACTfolding01 => fexpose_folding01 (vpw, vph)
      | ACTfolding02 => fexpose_folding02 (vpw, vph)
      | ACTrandom01 => fexpose_random01 (vpw, vph)
      | ACTrandom02 => fexpose_random02 (vpw, vph)
      | ACTrandom03 => fexpose_random03 (vpw, vph)
      | _(*0*) => fexpose_present (vpw, vph)
    ) : void // end of [val]
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
void
timeout_add_val (uint ntime) {
  if (timeout_id == 0) {
    timeout_id = g_timeout_add (ntime, (GSourceFunc)ftimeout, NULL);
  } ; return ;
} // end of [timeout_add_val]
//
void timeout_remove () {
  if (timeout_id != 0) {
    g_source_remove (timeout_id); timeout_id = 0;
  } ; return ;
} // end of [timeout_remove]
//
%} // end of [%{$]

macdef TIMEOUT_INTERVAL = 200U
macdef TIMEOUT_INTERVAL_ROT = 50U
extern
fun timeout_add_val
  (ntime: uint): void = "timeout_add_val"
fun timeout_add_rot () = timeout_add_val (TIMEOUT_INTERVAL_ROT)

extern fun timeout_remove (): void = "timeout_remove"

(* ****** ****** *)

val rotate_ref = ref_make_elt<int> (0)

(* ****** ****** *)

extern
fun ftimeout (): gboolean = "ftimeout"
implement
ftimeout () = let
//
  val act = theActState_get ()
  val () = if
    (act > 0) then {
    val alpha = !theAlpha_ref + theDelta
//
    val isRot = alpha <= 180.0
    val () = if isRot then let
      // more rotation is needed
    in
      !theAlpha_ref := alpha
    end // end of [val]
    val () = if ~(isRot) then let
      // rotation is completed by now
      val () = !rotate_ref := 0
      val () = !theRotateknd_ref := randint (2)
      val () = theSlideCount_inc ()
      val () = theActState_set (ACTpresent)
      val () = timeout_remove ()
      val () = timeout_add_val (TIMEOUT_INTERVAL)
    in
      !theAlpha_ref := 0.0
    end // end of [val]
  } // end of [if]
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
//
  val () = theSlideCount_dec ()
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
//
if (x = 0) then let
  val rotknd = 1 + randint(11)
  val () = theActState_set (rotknd)
  val () = timeout_remove ()
  val () = timeout_add_rot ()
in
  // nothing
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
//
in
  // nothing
end // end of [if]
//
end // end of [fnext]

(* ****** ****** *)

extern
fun fgoto (): void
implement fgoto () = let
//
  val spinner = theSpinner_get ()
  val n = gtk_spin_button_get_value (spinner)
  val () = theSlideCount_set (int_of(double_of(n)))
  val () = g_object_unref (spinner)
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
end // end of [fgoto]

(* ****** ****** *)

fun
map_event (): gboolean = let
(*
  val () = println! ("map_event: enter")
*)
  val () = if (!rotate_ref = 1) then timeout_add_rot () in GTRUE
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
    if (event.state = GDK_VISIBILITY_FULLY_OBSCURED) then timeout_remove () else timeout_add_rot ()
  // end of [if]
in
  GTRUE
end // end of [visibility_notify_event]

(* ****** ****** *)

macdef gs = gstring_of_string
overload gint with gint_of_GtkResponseType

(* ****** ****** *)

fun cb_key_press
  {l:agz} (
  win: !GtkWindow_ref (l), event: &GdkEventKey, data: gpointer
) : gboolean = let
  val kv = event.keyval
in
//
case+ 0 of
| _ when kv=(guint)GDK_Escape => let
    val btn = theButtonClose_get ()
    val () = g_signal_emit_by_name (btn, (gsignal)"clicked")
    val () = g_object_unref (btn)
  in
    GTRUE
  end // end of [_ when ...]
| _ when (
    kv=(guint)GDK_Up orelse kv=(guint)GDK_Left
  ) => let
    val btn = theButtonPrev_get ()
    val () = g_signal_emit_by_name (btn, (gsignal)"clicked")
    val () = g_object_unref (btn)
  in
    GTRUE
  end // end of [_ when ...]
| _ when (
    kv=(guint)GDK_Down orelse kv=(guint)GDK_Right
  ) => let
    val btn = theButtonNext_get ()
    val () = g_signal_emit_by_name (btn, (gsignal)"clicked")
    val () = g_object_unref (btn)
  in
    GTRUE
  end // end of [_ when ...]
| _ when (
    kv=(guint)GDK_space
  ) => let
    val () = theSlideCount_inc ()
    val btn = theButtonGoto_get ()
    val () = g_signal_emit_by_name (btn, (gsignal)"clicked")
    val () = g_object_unref (btn)
  in
    GTRUE
  end // end of [_ when ...]
| _ when (
    kv=(guint)GDK_Return
  ) => let
    val spinner = theSpinner_get ()
    val () = gtk_spin_button_update (spinner)
    val () = g_object_unref (spinner)
    val btn = theButtonGoto_get ()
    val () = g_signal_emit_by_name (btn, (gsignal)"clicked")
    val () = g_object_unref (btn)
  in
    GTRUE
  end // end of [_ when ...]
| _ => GFALSE
//
end // end of [cb_key_press]

(* ****** ****** *)

fun
cb_btn_close_clicked {l:agz}
  (btn: ptr, win: !GtkWindow_ref (l)): gboolean = GTRUE where {
(*
  val () = (print (#LOCATION + ": cb_btn_close_clicked"); print_newline ())
*)
  val flags = GTK_DIALOG_DESTROY_WITH_PARENT
  val _type = GTK_MESSAGE_QUESTION
  val buttons = GTK_BUTTONS_YES_NO
//
  val (fpf_x | x) = (gs)"Quit?"
  val dialog = gtk_message_dialog_new0 (flags, _type, buttons, x)
  prval () = fpf_x (x)
  val (fpf_x | x) = (gs)"Confirmation"
  val () = gtk_window_set_title (dialog, x)
  prval () = fpf_x (x)
//
  val () = gtk_window_set_transient_for (dialog, win(*parent*))
//
  val res = gtk_dialog_run (dialog)
  val () = gtk_widget_destroy0 (dialog)
//
  val () = case+ 0 of
    | _ when res = (gint)GTK_RESPONSE_YES => gtk_main_quit () // many things to do here!
    | _ => () // quit is not confirmed
  // end of [val]
} // end of [cb_file_quit_activate]

(* ****** ****** *)

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
val (fpf_x | x) = (gs)"gtkglSlidePresent"
val () = gtk_window_set_title (window, x)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (window, (gsignal)"delete_event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
val _sid = g_signal_connect
  (window, (gsignal)"key_press_event", G_CALLBACK (cb_key_press), (gpointer)null)
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
val () = theButtonClose_initset (btn_close)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (btn_close, (gsignal)"clicked", G_CALLBACK(cb_btn_close_clicked), (gpointer_vt)window)
// end of [val]
val () = gtk_box_pack_end (hbox1, btn_close, GFALSE, GFALSE, (guint)10)
val () = gtk_widget_show_unref (btn_close)
//
val (fpf_x | x) = (gs)"_Prev"
val btn_prev = gtk_button_new_with_mnemonic (x)
val () = theButtonPrev_initset (btn_prev)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (btn_prev, (gsignal)"clicked", G_CALLBACK(fprev), (gpointer)null)
// end of [val]
val () = gtk_box_pack_start (hbox1, btn_prev, GFALSE, GFALSE, (guint)4)
val () = gtk_widget_show_unref (btn_prev)
//
val (fpf_x | x) = (gs)"_Next"
val btn_next = gtk_button_new_with_mnemonic (x)
val () = theButtonNext_initset (btn_next)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (btn_next, (gsignal)"clicked", G_CALLBACK(fnext), (gpointer)null)
val () = gtk_box_pack_start (hbox1, btn_next, GFALSE, GFALSE, (guint)4)
val () = gtk_widget_show_unref (btn_next)
//
val (fpf_x | x) = (gs)"_Goto"
val btn_goto = gtk_button_new_with_mnemonic (x)
val () = theButtonGoto_initset (btn_goto)
prval () = fpf_x (x)
val _sid = g_signal_connect
  (btn_goto, (gsignal)"clicked", G_CALLBACK(fgoto), (gpointer)null)
val () = gtk_box_pack_start (hbox1, btn_goto, GFALSE, GFALSE, (guint)4)
val () = gtk_widget_show_unref (btn_goto)
//
val adj = gtk_adjustment_new (
  0.0(*ini*), 0.0(*min*), 999.0(*max*), 1.0(*inc*), 5.0(*pinc*), 0.0(*psize*)
) // end of [val]
val spinner = gtk_spin_button_new (adj, (gdouble)0.0, (guint)0)
val () = g_object_unref (adj)
val () = theSpinner_initset (spinner)
val () = gtk_spin_button_set_wrap (spinner, GTRUE)
val () = gtk_box_pack_start (hbox1, spinner, GFALSE, GTRUE, (guint)0)
val () = gtk_widget_show_unref (spinner)
//
val () = gtk_widget_show_unref (hbox1)
//
val () = gtk_widget_show_unref (vbox0)
//
val () = gtk_widget_show_unref (window)
//
(*
val () = timeout_add_val (TIMEOUT_INTERVAL) // start the clock
*)
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

char *the_myslide_dirname = "data" ;

ats_ptr_type
myslide_dirname_get () {
  return the_myslide_dirname ;
} // end of [myslide_dirname_get]

ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  int gtkglcheck ;
  GdkGLConfig *glconfig ;
//
  if (argc >= 2) {
    the_myslide_dirname = ((char**)argv)[1] ;
  } // end of [if]
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

(* end of [gtkglCS112Intro.dats] *)
