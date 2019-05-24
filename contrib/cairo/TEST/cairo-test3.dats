(*
**
** A simple CAIRO example: regular polygon
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2009
**
*)

(*
** how to compile:
   atscc -o test3 \
     `pkg-config --cflags --libs cairo` \
     $ATSHOME/contrib/cairo/atsctrb_cairo.o \
     cairo-test3.dats

** how ot test:
   ./test3
   'gthumb' can be used to view the generated image file 'cairo-test3.png'
*)

(* ****** ****** *)

staload M = "libc/SATS/math.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

stadef dbl = double
stadef cr (l:addr) = cairo_ref (l)

fun draw_reg_polygon
  {l:agz} {n:nat | n >= 3}
  (cr: !cr l, n: int n): void = let
  val agl_delta = 2 * $M.M_PI / n
  fun loop {i:nat | i <= n} .<n-i>.
    (cr: !cr l, agl0: dbl, i: int i):<cloref1> void =
    if i < n - 1 then let
      val agl1 = agl0 + agl_delta
      val () = cairo_line_to (cr, $M.cos agl1, $M.sin agl1)
    in
      loop (cr, agl1, i + 1)
    end else let
      val () = cairo_line_to (cr, 1.0, 0.0)
    in
      // nothing
    end // end of [if]
  // end of [loop]
  val () = cairo_move_to (cr, 1.0, 0.0)
  val () = loop (cr, 0.0, 0)
in
  // nothing
end // end of [draw_reg_polygon]

(* ****** ****** *)

fn draw_circle {l:agz} (
    cr: !cr l, rad: dbl, x0: dbl, y0: dbl
  ) : void = let
  val n0 = 8
  val agl0 = 2 * $M.M_PI / n0
  val n = loop (rad, n0, agl0) where {
    fun loop {n:int | n >= 8}
      (rad: dbl, n: int n, agl: double): intGte 8 =
      if (rad * agl > 1.0) then
        loop (rad, 2 * n, agl / 2)
      else
        n // loop exits
      // end of [if]
    // end of [loop]
  } // end of [val]
  val (pf | ()) = cairo_save (cr)
  val () = cairo_scale (cr, rad, rad)
  val () = draw_reg_polygon (cr, n)
  val () = cairo_restore (pf | cr)
in
  // nothing
end // end of [draw_circle]

(* ****** ****** *)

#define ALPHA 0.90

implement main () = () where {
  val surface =
    cairo_image_surface_create (CAIRO_FORMAT_ARGB32, 200, 200)
  val cr = cairo_create (surface)
  val x = 100.0 and y = 100.0
  val () = cairo_translate (cr, x, y)
  val () = cairo_rotate (cr, ~($M.M_PI) / 2)
  val (pf | ()) = cairo_save (cr)
  val sx = ALPHA * 100.0 and sy = ALPHA * 100.0
  val () = cairo_scale (cr, sx, sy)
  val () = draw_reg_polygon (cr, 5)
  val () = cairo_fill (cr)
  val () = cairo_restore (pf | cr)
  val () = draw_circle (cr, ALPHA * 100.0, x, y)
  val () = cairo_stroke (cr)
//
  val status = cairo_surface_write_to_png (surface, "cairo-test3.png")
  val () = cairo_surface_destroy (surface)
  val () = cairo_destroy (cr)
//
  val () = if status = CAIRO_STATUS_SUCCESS then begin
    print "The image is written to the file [cairo-test3.png].\n"
  end else begin
    print "exit(ATS): [cairo_surface_write_to_png] failed"; print_newline ()
  end // end of [if]
} // end of [main]

(* ****** ****** *)

(* end of [cairo-test3.dats] *)
