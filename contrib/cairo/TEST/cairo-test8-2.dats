(*
**
** A simple CAIRO example: an illusion of circular motion
** see Kitaoka's page: http://www.ritsumei.ac.jp/~akitaoka/
**
** This is a variant of cairo-test8-1
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: February, 2010
**
*)

(*
** how to compile:
**   atscc -o test8-2 `pkg-config --cflags --libs cairo` cairo-test8-2.dats -lX11
**
** how ot test:
**   ./test8-2
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
// end of [bw_set]

fn yb_set {l:agz}
  (cr: !cr l, yb: int): void =
  if yb > 0 then
    cairo_set_source_rgb (cr, 1.0, 0.75, 0.0)
  else
    cairo_set_source_rgb (cr, 0.0, 0.0, 1.0)
  // end of [if]
// end of [yb_set]

(* ****** ****** *)

fn draw_ring
  {l:agz} {n:int | n >= 2} (
    cr: !cr l
  , bw: int, yb: int
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
    (cr: !cr l, angle: double, i: int i, yb: int)
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
    val () = yb_set (cr, yb)
    val () = cairo_fill (cr)
  in
    if i < n then loop2 (cr, angle+delta, i+1, 1-yb)
  end // end of [loop2]
  val () = loop2 (cr, 0.0, 1, yb)
in
  // nothing
end // end of [draw_ring]

(* ****** ****** *)

#define SHRINKAGE 0.81
fun draw_rings
  {l:agz} {n:int | n >= 2} (
    cr: !cr l
  , bw: int, yb: int
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
    val () = draw_ring (cr, bw, yb, rad_beg, rad_beg_nxt, n)
  in
    draw_rings (cr, 1-bw, 1-yb, rad_beg_nxt, rad_end, n)
  end // end of [if]
// end of [draw_rings]

(* ****** ****** *)

staload "contrib/X11/SATS/X.sats"
staload "contrib/X11/SATS/Xlib.sats"

(* ****** ****** *)

symintr uint
overload uint with uint_of_int // no-op casting

(* ****** ****** *)

macdef double = double_of

fun draw_all {l:agz} (
    dpy: !Display_ptr l, win: Window, wd: int, ht: int
  ) :<cloref1> void = () where {
  val screen_num = XDefaultScreen (dpy)
//
  val (pf_minus | visual) = XDefaultVisual (dpy, screen_num)
  val surface = cairo_xlib_surface_create (dpy, (Drawable)win, visual, wd, ht)
  prval () = minus_addback (pf_minus, visual | dpy)
//
  val mn = min (wd, ht)
  val xmargin = double (wd - mn) / 2
  val ymargin = double (ht - mn) / 2
  val cr = cairo_create (surface)
  val () = cairo_surface_destroy (surface)
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
  val () = cairo_destroy (cr)
} // end of [draw_all]

(* ****** ****** *)

implement main () = () where {
  val wd0 = 512 and ht0 = 512
//
  val [l_dpy:addr] dpy = XOpenDisplay (stropt_none)
  val () = assert_errmsg (Display_ptr_isnot_null dpy, #LOCATION)
//
  val screen_num = XDefaultScreen (dpy)
  val mywin = XCreateSimpleWindow (
    dpy, parent, x, y, width, height, border_width, w_pix, b_pix
  ) where {
    val parent = XRootWindow (dpy, screen_num)
    val x = 0 and y = 0
    val width = (uint)wd0 and height = (uint)ht0
    val border_width = (uint)4
    val w_pix = XWhitePixel (dpy, screen_num)
    val b_pix = XBlackPixel (dpy, screen_num)
  } // end of [val]
//
  val () = XMapWindow(dpy, mywin)
//
  val () = XSelectInput (dpy, mywin, flag) where {
    val flag = ExposureMask lor KeyPressMask lor ButtonPressMask lor StructureNotifyMask
  } // end of [val]
//
  var report: XEvent? // uninitialized
  val () = while (true) let
    val () = XNextEvent (dpy, report)
    val type = report.type
  in
    case+ 0 of
    | _ when (type = Expose) => () where {
        prval (pf, fpf) = XEvent_xexpose_castdn (view@ report)
        val count = (&report)->count
        val () =  if count = 0 then let
          val wd = (&report)->width and ht = (&report)->height
        in
          draw_all (dpy, mywin, wd, ht)
        end (* end of [if] *)
        prval () = view@ report := fpf (pf)
      } // end of [Expose]
    | _ when (type = KeyPress) => (break)
    | _ => () // ignored
  end // end of [val]
//
  val () = XCloseDisplay (dpy)
//
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test8-2.dats] *)
