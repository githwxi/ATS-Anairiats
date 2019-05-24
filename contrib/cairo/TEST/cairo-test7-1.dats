(*
**
** A simple CAIRO example: a clock @ home
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(*
** how to compile:
   atscc -o test7-1 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test7-1.dats

** how ot test:
   ./test7-1
   'gthumb' can be used to view the generated image file 'cairo-test7-1.png'
*)

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

stadef dbl = double
stadef cr (l:addr) = cairo_ref l

(* ****** ****** *)

fn draw_hand {l:agz}
  (cr: !cr l, bot: dbl, top:dbl, len: dbl): void = let
  val () = cairo_move_to (cr, 0.0, bot/2)
  val () = cairo_line_to (cr, len, top/2)
  val () = cairo_line_to (cr, len, ~top/2)
  val () = cairo_line_to (cr, 0.0, ~bot/2)
  val () = cairo_close_path (cr)
in
  cairo_fill (cr)
end // end of [draw_hand]

fn draw_clock
  {l:agz} {w,h:nat} (
    cr: !cr l
  , wd: int w, ht: int h
  , h: natLt 24, m: natLt 60
  ) : void = let
//
  val h = (if h >= 12 then h - 12 else h): natLt 12
  val m_ang = m * (M_PI / 30) - M_PI/2
  val h_ang = h * (M_PI / 6) + m * (M_PI / 360) - M_PI/2
//
  val wd = double_of (wd)
  and ht = double_of (ht)
  val mn = min (wd, ht)
  val rad = 0.375 * mn
  val (pf0 | ()) = cairo_save (cr)
  val xc = wd / 2 and yc = ht / 2
  val () = cairo_translate (cr, xc, yc)
  val () = cairo_arc
    (cr, 0.0, 0.0, rad, 0.0, 2 * M_PI)
  val () = cairo_set_source_rgb (cr, 1.0, 1.0, 1.0)
  val () = cairo_fill (cr)
  val () = cairo_arc
    (cr, 0.0, 0.0, rad, 0.0, 2 * M_PI)
  val () = cairo_set_source_rgb (cr, 0.0, 1.0, 0.0)
  val () = cairo_set_line_width (cr, 10.0)
  val () = cairo_stroke (cr)
//
  val rad1 = 0.90 * rad
  val () = cairo_arc (cr, ~rad1, ~rad1, rad1, 0.0,  M_PI/2)
  val () = cairo_arc (cr, ~rad1,  rad1, rad1, ~M_PI/2, 0.0)
  val () = cairo_arc (cr,  rad1,  rad1, rad1, ~M_PI, ~M_PI/2)
  val () = cairo_arc (cr,  rad1, ~rad1, rad1, M_PI/2, M_PI)
  val () = cairo_fill (cr)
//
  val h_l = 0.60 * rad
  val (pf | ()) = cairo_save (cr)
  val () = cairo_rotate (cr, h_ang)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = draw_hand (cr, 6.0, 6.0/2, h_l)
  val () = cairo_restore (pf | cr)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_rotate (cr, h_ang+M_PI)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = draw_hand (cr, 6.0, 6.0/2, h_l/4)
  val () = cairo_restore (pf | cr)
//
  val m_l = 0.85 * rad
  val (pf | ()) = cairo_save (cr)
  val () = cairo_rotate (cr, m_ang)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = draw_hand (cr, 5.0, 5.0/2, m_l)
  val () = cairo_restore (pf | cr)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_rotate (cr, m_ang+M_PI)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = draw_hand (cr, 5.0, 5.0/2, h_l/4)
  val () = cairo_restore (pf | cr)
//
  val () = cairo_new_sub_path (cr)
  val () = cairo_arc (cr, 0.0, 0.0, 7.2, 0.0, 2 * M_PI)  
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_fill (cr)
  val () = cairo_restore (pf0 | cr)
in
  // nothing
end // end of [draw_clock]

(* ****** ****** *)

staload "libc/SATS/time.sats"

implement main () = () where {
//
  val wd0 = 300 and ht0 = 300  
//
  var t: time_t // unintialized
  val yn = time_get_and_set (t)
  val () = assert_errmsg (yn, #LOCATION)
  prval () = opt_unsome {time_t} (t)
  var tm: tm_struct // unintialized
  val _ptr = localtime_r (t, tm)
  val () = assert_errmsg (_ptr > null, #LOCATION)
  prval () = opt_unsome {tm_struct} (tm)
  val hr = tm.tm_hour and min = tm.tm_min
  val hr = int1_of_int (hr)
  val () = assert (0 <= hr && hr < 24)
  val min = int1_of_int (min)
  val () = assert (0 <= min && min < 60)
//
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, wd0, ht0)
  val cr = cairo_create (surface)
//
  val () = draw_clock (cr, wd0, ht0, hr, min)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test7-1.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test7-1.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test7-1.dats] *)
