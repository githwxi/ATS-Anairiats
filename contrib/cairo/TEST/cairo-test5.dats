(*
**
** A simple CAIRO example: negative arc
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(*
** how to compile:
   atscc -o test5 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test5.dats

** how ot test:
   ./test5
   'gthumb' can be used to view the generated image file 'cairo-test5.png'
*)

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

stadef dbl = double
stadef cr (l:addr) = cairo_ref l

(* ****** ****** *)

implement main () = () where {
//
  val wsf = 300 and hsf = 300
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, wsf, hsf)
  val cr = cairo_create (surface)
//
  val wsf = double_of wsf and hsf = double_of hsf
  val xc = wsf / 2 and yc = hsf / 2
  val rad = min (wsf, hsf) / 3
  val th1 = 45 * (M_PI / 180)
  val th2 = 180 * (M_PI / 180)
  val () = cairo_set_line_width (cr, 10.0)
  val () = cairo_arc_negative (cr, xc, yc, rad, th1, th2)
  val () = cairo_stroke (cr)
  val () = cairo_set_source_rgba (cr, 1.0, 0.2, 0.2, 0.6);
  val () = cairo_set_line_width (cr, 6.0)
  val () = cairo_arc (cr, xc, yc, 10.0, 0.0, 2*M_PI)
  val () = cairo_fill (cr)
  val () = cairo_move_to (cr, xc, yc)
  val () = cairo_line_to (cr, xc+rad*cos(th1), yc+rad*sin(th1))
  val () = cairo_move_to (cr, xc, yc)
  val () = cairo_line_to (cr, xc+rad*cos(th2), yc+rad*sin(th2))
  val () = cairo_stroke (cr)
  val status = cairo_surface_write_to_png (surface, "cairo-test5.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test5.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test5.dats] *)
