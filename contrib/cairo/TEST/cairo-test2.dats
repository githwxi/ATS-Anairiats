(*
**
** A simple CAIRO example: rounded rectangle
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(*
** how to compile:
   atscc -o test2 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test2.dats

** how ot test:
   ./test2
   'gthumb' can be used to view the generated image file 'cairo-test2.png'
*)

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

stadef dbl = double
stadef cr = cairo_ref1

fun draw_rounded_rectangle .<>. (
    cr: !cr, x: dbl, y: dbl, w: dbl, h:dbl, r: dbl
  ) : void = let
  val () = cairo_move_to (cr, x+r, y)
  val () = cairo_line_to (cr, x+w-r, y)
  val () = cairo_curve_to (cr, x+w, y, x+w, y, x+w, y+r)
  val () = cairo_line_to (cr, x+w, y+h-r)
  val () = cairo_curve_to (cr, x+w, y+h, x+w, y+h, x+w-r, y+h)
  val () = cairo_line_to (cr, x+r, y+h)
  val () = cairo_curve_to (cr, x, y+h, x, y+h, x, y+h-r)
  val () = cairo_line_to (cr, x, y+r)
  val () = cairo_curve_to (cr, x, y, x, y, x+r, y)
  val () = cairo_stroke (cr)
in
  // nothing
end // end of [draw_rounded_rectangle]
   
(* ****** ****** *)

implement main () = () where {
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, 200, 200)
  val cr = cairo_create (surface)
//
  val x = 50.0
  val y = 50.0
  val w = 100.0
  val h = 100.0
  val r = 10.0
//  
  val () = draw_rounded_rectangle (cr, x, y, w, h, r)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test2.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test2.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test2.dats] *)
