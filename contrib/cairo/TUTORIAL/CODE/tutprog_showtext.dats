(*
**
** ATS/Cairo Tutorial: Drawing Text
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: 2010-04-30
**
*)

(*
** Copyright (C) 2009-2010 Hongwei Xi, Boston University
**
** Permission is hereby granted, free of charge, to any person
** obtaining a copy of this software and associated documentation
** files (the "Software"), to deal in the Software without
** restriction, including without limitation the rights to use,
** copy, modify, merge, publish, distribute, sublicense, and/or sell
** copies of the Software, and to permit persons to whom the
** Software is furnished to do so, subject to the following
** conditions:
**
** The above copyright notice and this permission notice shall be
** included in all copies or substantial portions of the Software.
**
** THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
** EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
** OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
** NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
** HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
** WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
** FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
** OTHER DEALINGS IN THE SOFTWARE.
*)

(* ****** ****** *)
//
// How to compile:
//   atscc -o tutprog_showtext tutprog_showtext.dats `pkg-config cairo --cflags --libs`
//
// How to test:
//   ./tutprog_showtext
//
(* ****** ****** *)

staload "libc/SATS/math.sats"
macdef PI = M_PI

(* ****** ****** *)
//
staload "contrib/cairo/SATS/cairo.sats"
//
extern
fun cairo_text_extents {l:agz} (
    cr: !cairo_ref l, utf8: string
  , extents: &cairo_text_extents_t? >> cairo_text_extents_t
  ) : void = "mac#atsctrb_cairo_text_extents"
// end of [cairo_text_extents]
//
extern
fun cairo_text_path {l:agz}
  (cr: !cairo_ref l, text: string): void = "mac#atsctrb_cairo_text_path"
// end of [cairo_text_path]
//
(* ****** ****** *)

fun showtext {l:agz} (
  cr: !cairo_ref l, utf8: string
) : void = () where {
  var te : cairo_text_extents_t
  val () = cairo_text_extents (cr, utf8, te)
//
  val width = te.width
  and height = te.height
  val x_base = te.width / 2 + te.x_bearing
  and y_base = ~te.y_bearing / 2
//
  val (pf0 | ()) = cairo_save (cr)
//
  val () = cairo_rectangle (cr, ~width / 2, ~height/ 2, width, height)
  val () = cairo_set_source_rgb (cr, 0.5, 0.5, 1.0)
  val () = cairo_fill (cr)
//
  #define RAD 2.0
  val () = cairo_arc (cr, ~x_base, y_base, RAD, 0.0, 2*PI)
  val () = cairo_set_source_rgb (cr, 1.0, 0.0, 0.0) // red
  val () = cairo_fill (cr)
//
  val () = cairo_arc (cr, ~x_base+te.x_advance, y_base+te.y_advance, RAD, 0.0, 2*PI)
  val () = cairo_set_source_rgb (cr, 1.0, 0.0, 0.0) // red
  val () = cairo_fill (cr)
//
  val () = cairo_move_to (cr, ~x_base, y_base)
  val () = cairo_text_path (cr, utf8)
  val () = cairo_set_source_rgb (cr, 0.25, 0.25, 0.25) // dark gray
  val () = cairo_fill (cr)
//
  val () = cairo_restore (pf0 | cr)
//
} // end of [showtext]

(* ****** ****** *)

implement main () = () where {
  val W = 300 and H = 60
  val sf = cairo_image_surface_create (CAIRO_FORMAT_ARGB32, W, H)
  val cr = cairo_create (sf)
//
  #define FONTSIZE 20
  val () = cairo_select_font_face
    (cr, "Georgia", CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD)
  val () = cairo_set_font_size (cr, (double_of)FONTSIZE)
//
  val () = cairo_translate (cr, 1.0*W/2, 1.0*H/2)
  // val () = cairo_rotate (cr, ~atan2 (1.0*H, 1.0*W))
  val () = cairo_scale (cr, 2.5, 2.5)
  val () = showtext (cr, "Top Secret")
//
  val status = cairo_surface_write_to_png (sf, "tutprog_showtext.png")
  val () = cairo_surface_destroy (sf) // a type error if omitted
  val () = cairo_destroy (cr) // a type error if omitted
//
  // in case of a failure ...
  val () = assert_errmsg (status = CAIRO_STATUS_SUCCESS, #LOCATION)
} // end of [main]

(* ****** ****** *)

(* end of [tutprog_showtext.dats] *)
