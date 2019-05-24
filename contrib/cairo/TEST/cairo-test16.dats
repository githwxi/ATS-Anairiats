(*
**
** A simple CAIRO example: text alignment
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010
**
*)

(*
** how to compile:
   atscc -o test16 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test16.dats

** how ot test:
   ./test16
   'gthumb' can be used to view the generated image file 'cairo-test16.png'
*)

(* ****** ****** *)

staload M = "libc/SATS/math.sats"
macdef PI = $M.M_PI

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

implement main () = () where {
  val utf8 = "cairo"
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, 256, 256)
  val cr = cairo_create (surface)
//
  val () = cairo_select_font_face
    (cr, "Sans", CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_NORMAL)
  // end of [val]
  val () = cairo_set_font_size (cr, 52.0)
  var extents: cairo_text_extents_t
//
  val () = cairo_text_extents (cr, utf8, extents)
  val x = 128.0 - (extents.width / 2 + extents.x_bearing)
  val y = 128.0 - (extents.height / 2 + extents.y_bearing)
  val () = cairo_move_to (cr, x, y)
  val () = cairo_show_text (cr, utf8)
//
  val () = cairo_set_source_rgba (cr, 1.0, 0.2, 0.2, 0.6)
  val () = cairo_set_line_width (cr, 6.0)
  val () = cairo_arc (cr, x, y, 10.0, 0.0, 2*PI)
  val () = cairo_fill (cr)
  val () = cairo_move_to (cr, 0.0, 128.0)
  val () = cairo_rel_line_to (cr, 256.0, 0.0)
  val () = cairo_move_to (cr, 128.0, 0.0)
  val () = cairo_rel_line_to (cr, 0.0, 256.0)
  val () = cairo_stroke (cr)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test16.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test16.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test16.dats] *)
