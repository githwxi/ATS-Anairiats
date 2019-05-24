(*
** generating images for atslangweb
**
** Author: Hongwei Xi (gmhwxi AT gmail DOT com)
** Start Time: August, 2011
**
*)

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

stadef dbl = double
stadef cr (l:addr) = cairo_ref l

(* ****** ****** *)

extern fun
genGradientSegImage (
  filename: string, wsf: int
, r1: double, g1: double, b1: double
, r2: double, g2: double, b2: double
) : void
// end of [thePageBody_bgimage]

implement
genGradientSegImage
  (filename, wsf, r1, g1, b1, r2, g2, b2) = let
(*
  val () = println! ("wsf = ", wsf)
*)
  val hsf = 1(*pix*)
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, wsf, hsf)
  val cr = cairo_create (surface)
//
  val wsf = (double_of)wsf
  val hsf = (double_of)hsf
//
  val pat = cairo_pattern_create_linear (0.0, 0.0, wsf, 0.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 0.0, r1, g1, b1, 1.0)
  val () = cairo_pattern_add_color_stop_rgba (pat, 1.0, r2, g2, b2, 1.0)
  val () = cairo_set_source (cr, pat)
  val () = cairo_pattern_destroy (pat)
  val () = cairo_rectangle (cr, 0.0, 0.0, wsf, hsf)
  val () = cairo_fill (cr)
//
  val status = cairo_surface_write_to_png (surface, filename)
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
  val () = if status != CAIRO_STATUS_SUCCESS then begin
    prerrf ("exit(ATS): [cairo_surface_write_to_png] failed.\n", @())
  end // end of [if]
in
//
//  prerrf ("The image is written to the file [%s].\n", @(filename))
//
end // end of [genGradientSegImage]

(* ****** ****** *)

#include "atslangweb_params.hats"

(* ****** ****** *)

implement
main () = {
//
  val filename = "images/theSidebar_bgimage.png"
  val wsf = theSidebar_width
//
  val r1 = 0.375 * 0.50
  val g1 = 0.375 * 0.75
  val b1 = 0.375 * 1.00
//
  val r2 = 0.875 * 0.50
  val g2 = 0.875 * 0.75
  val b2 = 0.875 * 1.00
//
  val () = genGradientSegImage (filename, wsf, r1, g1, b1, r2, g2, b2)
//
  val filename = "images/thePageBody_bgimage.png"
  val wsf = 1600(*pix*)
//
  val r1 = 0.975 * 0.950
  val g1 = 0.975 * 0.950
  val b1 = 0.975 * 1.000
//
  val r2 = 0.999 * 0.999
  val g2 = 0.999 * 0.999
  val b2 = 0.999 * 1.000
//
  val () = genGradientSegImage (filename, wsf, r1, g1, b1, r2, g2, b2)
//
} // end of [main]

(* ****** ****** *)

(* end of [atslangweb_bgimages.dats] *)
