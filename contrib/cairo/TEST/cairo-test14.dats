(*
**
** A simple CAIRO example: joint styles
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010
**
*)

(*
** how to compile:
   atscc -o test14 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test14.dats

** how ot test:
   ./test14
   'gthumb' can be used to view the generated image file 'cairo-test14.png'
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
  val () = cairo_set_line_width (cr, 40.96)
//
  val () = cairo_move_to (cr, 76.8, 84.48)
  val () = cairo_rel_line_to (cr, 51.2, ~51.2)
  val () = cairo_rel_line_to (cr, 51.2,  51.2)
  val () = cairo_set_line_join (cr, CAIRO_LINE_JOIN_MITER)
  val () = cairo_stroke (cr)
//
  val () = cairo_move_to (cr, 76.8, 161.28)
  val () = cairo_rel_line_to (cr, 51.2, ~51.2)
  val () = cairo_rel_line_to (cr, 51.2,  51.2)
  val () = cairo_set_line_join (cr, CAIRO_LINE_JOIN_BEVEL)
  val () = cairo_stroke (cr)
//
  val () = cairo_move_to (cr, 76.8, 238.08)
  val () = cairo_rel_line_to (cr, 51.2, ~51.2)
  val () = cairo_rel_line_to (cr, 51.2,  51.2)
  val () = cairo_set_line_join (cr, CAIRO_LINE_JOIN_ROUND)
  val () = cairo_stroke (cr)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test14.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test14.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test14.dats] *)
