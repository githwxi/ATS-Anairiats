(*
**
** A simple CAIRO example: line cap styles
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010
**
*)

(*
** how to compile:
   atscc -o test13 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test13.dats

** how ot test:
   ./test13
   'gthumb' can be used to view the generated image file 'cairo-test13.png'
*)

(* ****** ****** *)

staload M = "libc/SATS/math.sats"
macdef PI = $M.M_PI

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

implement main () = () where {
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, 256, 256)
  val cr = cairo_create (surface)
//
  var x: double = 0.0
  val () = cairo_set_line_width (cr, 30.0)
//
  val () = x := x + 64
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_BUTT) // default
  val () = cairo_move_to (cr, x, 50.0)
  val () = cairo_line_to (cr, x, 200.0)
  val () = cairo_stroke (cr)
//
  val () = x := x + 64
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_ROUND)
  val () = cairo_move_to (cr, x, 50.0)
  val () = cairo_line_to (cr, x, 200.0)
  val () = cairo_stroke (cr)
//
  val () = x := x + 64
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_SQUARE)
  val () = cairo_move_to (cr, x, 50.0)
  val () = cairo_line_to (cr, x, 200.0)
  val () = cairo_stroke (cr)
//
// drawing help lines
//
  val () = x := 0.0
  val () = cairo_set_source_rgb (cr, 1.0, 0.2, 0.2)
  val () = cairo_set_line_width (cr, 2.56)
//
  val () = x := x + 64
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_BUTT) // default
  val () = cairo_move_to (cr, x, 50.0)
  val () = cairo_line_to (cr, x, 200.0)
  val () = cairo_stroke (cr)
//
  val () = x := x + 64
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_ROUND)
  val () = cairo_move_to (cr, x, 50.0)
  val () = cairo_line_to (cr, x, 200.0)
  val () = cairo_stroke (cr)
//
  val () = x := x + 64
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_SQUARE)
  val () = cairo_move_to (cr, x, 50.0)
  val () = cairo_line_to (cr, x, 200.0)
  val () = cairo_stroke (cr)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test13.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test13.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test13.dats] *)
