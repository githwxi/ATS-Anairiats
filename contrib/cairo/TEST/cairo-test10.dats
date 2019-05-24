(*
**
** A simple CAIRO example involving PS surface
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(*
** how to compile:
   atscc -o test10 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test10.dats

** how ot test:
   ./test10
   'gv' can be used to view the generated image file 'cairo-test10.ps'
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "contrib/cairo/SATS/cairo.sats"

#define PI M_PI

(* ****** ****** *)

stadef dbl = double
stadef cr (l:addr) = cairo_ref l

(* ****** ****** *)

fn draw_cross {l:agz} (
    cr: !cr l
  , x: double, y: double, sz: double
  ) : void = let
  val (pf | ()) = cairo_save (cr)
  val () = cairo_translate (cr, x, y)
  val sz2 = sz / 2
  val () = cairo_set_line_width (cr, sz/5)
  val () = cairo_move_to (cr, ~sz2, ~sz2)
  val () = cairo_line_to (cr,  sz2,  sz2)
  val () = cairo_stroke (cr)
  val () = cairo_move_to (cr,  sz2, ~sz2)
  val () = cairo_line_to (cr, ~sz2,  sz2)
  val () = cairo_stroke (cr)
  val () = cairo_restore (pf | cr)
in
  // nothing
end // end of [draw_cross]

(* ****** ****** *)

/*
//
// this is so clumsy!!! fortunately, it is no longer needed
//

%{^
double
cairo_font_extents_height (ats_ref_type x) {
  return ((cairo_font_extents_t*)x)->height ;
}

double
cairo_font_extents_max_x_advance (ats_ref_type x) {
  return ((cairo_font_extents_t*)x)->max_x_advance ;
}

double
cairo_text_extents_width (ats_ref_type x) {
  return ((cairo_text_extents_t*)x)->width ;
}
%}
extern
fun cairo_font_extents_height (x: &cairo_font_extents_t):<> double
  = "cairo_font_extents_height"

extern
fun cairo_text_extents_width (x: &cairo_text_extents_t):<> double
  = "cairo_text_extents_width"

extern
fun cairo_font_extents_max_x_advance (x: &cairo_font_extents_t):<> double
  = "cairo_font_extents_max_x_advance"
*/

(* ****** ****** *)

fn draw_table {l:agz}
  (cr: !cr l, w: double, fntsz: double): void = let
  val () = cairo_select_font_face
    (cr, "sans", CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD)
  val () = cairo_set_font_size (cr, fntsz)
  var fntexts : cairo_font_extents_t
  val () = cairo_font_extents (cr, fntexts)
  val () = cairo_set_line_width (cr, fntsz/10)
//
  val xdelta = w / 10
  val ydelta = 1.5 * fntexts.height
//
  var x: dbl = 0.0
  var y: dbl = 0.0
  var i: int = 0
//
  val xlen: dbl = 10 * xdelta
  val ylen: dbl = 10 * ydelta
//
  val () = y := ydelta
  val () = for
    (i := 1; i < 10; i := i+1) let
    val () = cairo_move_to (cr, 0.0, y)
    val () = cairo_line_to (cr, xlen, y)
    val () = cairo_stroke (cr)
    val () = y := y + ydelta
  in
    // nothing
  end // end of [val]
//
  val () = x := xdelta
  val () = for
    (i := 1; i < 10; i := i+1) let
    val () = cairo_move_to (cr, x, 0.0)
    val () = cairo_line_to (cr, x, ylen)
    val () = cairo_stroke (cr)
    val () = x := x + xdelta
  in
    // nothing
  end // end of [val]
//
(*
  val () = printf ("fntexts.max_x_advance = %f\n", @(fntexts.max_x_advance))
*)
  val x_adj = fntexts.max_x_advance - 10.0 and y_adj = 5.0
//
  val () = draw_cross
    (cr, 0.65*xdelta, 0.90*fntsz, 0.75*fntsz)
//
  val () = x := 2*xdelta - x_adj and () = y := ydelta - y_adj
  val () = for
    (i := 1; i < 10; i := i+1) let
    val () = cairo_move_to (cr, x, y)
    val txt = tostrptr (i)
    val () = cairo_show_text (cr, $UN.castvwtp1{string} (txt))
    val () = strptr_free (txt)
    val () = x := x + xdelta
  in
    // nothing
  end // end of [val]
//
  val () = x := xdelta - x_adj
  val () = y := 2*ydelta - y_adj
  val () = for
    (i := 1; i < 10; i := i+1) let
    val () = cairo_move_to (cr, x, y)
    val txt = tostrptr (i)
    val () = cairo_show_text (cr, $UN.castvwtp1{string} (txt))
    val () = strptr_free (txt)
    val () = y := y + ydelta
  in
    // nothing
  end // end of [val]
//
  var j: int = 0
  val () = x := 2*xdelta - x_adj
  val () = y := 2*ydelta - y_adj
  val () = for
    (i := 1; i < 10; i := i+1) let
    val () = for
      (j := 1; j < 10; j := j+1) let
      val ij = i * j
      val d1 = ij / 10
      val d2 = ij mod 10
      val () = cairo_move_to (cr, x, y)
      val txt = tostrptr (d2)
      val () = cairo_show_text (cr, $UN.castvwtp1{string} (txt))
      val () = strptr_free (txt)
      val () = if d1 > 0 then let
        val () = cairo_move_to (cr, x - 0.60 * fntsz, y)
        val txt = tostrptr (d1)
        val () = cairo_show_text (cr, $UN.castvwtp1{string} (txt))
        val () = strptr_free (txt)
      in
        // nothing
      end // end of [val]
    in
      x := x + xdelta
    end // end of [for]
    val () = x := 2*xdelta - x_adj and () = y := y + ydelta
  in
    // nothing
  end // end of [for]
//
in
  // nothing
end // end of [draw_table]

(* ****** ****** *)

//
// letter: 8.5 x 11 (inches)
//

val x_letter = 8.5 * 72 and y_letter = 11.0 * 72

implement main () = () where {
  val wsf = 512 and hsf = 768
(*
  val sf =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, wsf, hsf)
  // end of [val]
*)
  val wsf = double_of wsf and hsf = double_of hsf
(*
  val sf = 
    cairo_pdf_surface_create ("cairo-test10.pdf", x_letter, y_letter)
  // end of [val]
*)
// (*
  val sf =
    cairo_ps_surface_create ("cairo-test10.ps", x_letter, y_letter)
  // end of [val]
  val () = cairo_ps_surface_dsc_comment (sf, "%%Title: Zoe's Multiplication Table")
  val () = cairo_ps_surface_dsc_comment (sf, "%%Copyright: Copyright (C) Hongwei Xi")
  val () = cairo_ps_surface_dsc_begin_setup (sf)
  val () = cairo_ps_surface_dsc_comment (sf, "%%IncludeFeatures: *MediaColor: White")
  val () = cairo_ps_surface_dsc_begin_page_setup (sf)
  val () = cairo_ps_surface_dsc_comment (sf, "%%IncludeFeatures: *PageSize Letter")
// *)
  val cr = cairo_create (sf)
//
  val () = cairo_translate (cr, (x_letter-wsf)/2, 72.0)
//
  val image =
    cairo_image_surface_create_from_png ("data/zoe-2006-05-27-1.png")
  // end of [val]
  val wimg = cairo_image_surface_get_width (image)
  val himg = cairo_image_surface_get_height (image)
  val () = printf ("wimg = %i and himg = %i\n", @(wimg, himg))
//
  val (pf | ()) = cairo_save (cr)
  val xrat = (1.0*250/512)
  val yrat = (1.0*224/768)
  val () = cairo_translate (cr, ~120.0/512*wsf, ~80.0/768*hsf)
  val () = cairo_arc (cr, xrat*wsf, yrat*hsf, 95.0, 0.0, 2*PI);
  val () = cairo_clip (cr)
  val xcoef = wsf / wimg
  val ycoef = hsf / himg
  val () = cairo_scale (cr, xcoef, ycoef)
  val () = cairo_set_source_surface (cr, image, 0.0, 0.0)
  val () = cairo_paint (cr)
  val () = cairo_restore (pf | cr)
  val () = cairo_surface_destroy (image)
//
  val () = cairo_select_font_face
    (cr, "serif", CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD)
  // end of [val]
  val () = cairo_set_font_size (cr, 24.0)
  val () = cairo_set_source_rgb (cr, 0.0, 0.0, 1.0)
//
  val title = "Zoe's Multiplication Table"
  var txtexts : cairo_text_extents_t
  val () = cairo_text_extents (cr, title, txtexts)
  val x_title = (wsf-txtexts.width)/2
  val () = cairo_move_to (cr, x_title, 272.0/768*hsf)
  val () = cairo_show_text (cr, title)
//
  val m_table = 72.0 // margin
  val x_table = m_table
  val (pf | ()) = cairo_save (cr)
  val () = cairo_translate (cr, x_table, 300.0)
  val w_table = 2*(wsf/2 - m_table)
  val () = draw_table (cr, w_table, 14.0(*fntsz*))
  val () = cairo_restore (pf | cr)
//
(*
  val status = cairo_surface_write_to_png (sf, "cairo-test10.png")
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test10.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
*)
// (*
  val () = cairo_show_page (cr)
// *)
  val () = cairo_surface_destroy (sf)
  val () = cairo_destroy (cr)
//
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test10.dats] *)
