(*
**
** A simple CAIRO example: text filling
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010
**
*)

(*
** how to compile:
   atscc -o test15 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test15.dats

** how ot test:
   ./test15
   'gthumb' can be used to view the generated image file 'cairo-test15.png'
*)

(* ****** ****** *)

staload M = "libc/SATS/math.sats"
macdef PI = $M.M_PI

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

implement main () = () where {
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, 300, 256)
  val cr = cairo_create (surface)
//
  val () = cairo_select_font_face
    (cr, "Sans", CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD)
  val () = cairo_set_font_size (cr, 90.0)
//
  val () = cairo_move_to (cr, 10.0, 135.0)
  val () = cairo_show_text (cr, "Hello")
//
  val () = cairo_move_to (cr, 70.0, 165.0)
  val () = cairo_text_path (cr, "void")
//
  val () = cairo_set_source_rgb (cr, 0.5, 0.5, 1.0)
  val () = cairo_fill_preserve (cr)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 0.0)
  val () = cairo_set_line_width (cr, 2.56)
  val () = cairo_stroke (cr)
//
// drawing help lines
//
  val () = cairo_set_source_rgba (cr, 1.0, 0.2, 0.2, 0.6)
  val () = cairo_arc (cr, 10.0, 135.0, 5.12, 0.0, 2*PI)
  val () = cairo_close_path (cr)
  val () = cairo_arc (cr, 70.0, 165.0, 5.12, 0.0, 2*PI)
  val () = cairo_fill (cr)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test15.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test15.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test15.dats] *)
