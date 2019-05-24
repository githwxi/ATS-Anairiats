(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -msse2 -O3 mandelbrot.dats -o mandelbrot
*)

#define TIMES 50
#define LIMIT2 (2.0 * 2.0)
#define i2b byte_of_int
#define i2d double_of_int

fn mandelbrot (h: int, w: int): void = let
  val w_r = 1.0 / i2d w and h_r = 1.0 / i2d h
  fn p (x: int, y: int):<cloref1> bool = let
    val Cr = i2d (2 * x) * w_r - 1.5
    and Ci = i2d (2 * y) * h_r - 1.0
    fun lp (r: double, i: double, k: int):<cloref1> bool =
      let val r2 = r * r and i2 = i * i in
        if r2+i2 <= LIMIT2 then
          if k=0 then true else lp (r2-i2+Cr, 2.0*r*i+Ci, k-1)
        else false
      end
  in
    lp (0.0, 0.0, TIMES)
  end

  fun xl (x: int, y: int, b: byte, n: natLte 8):<cloref1> void =
    if x < w then
      if p (x, y) then
        if n > 0 then xl (x+1, y, (b << 1) + i2b 1, n-1)
        else (print b; xl (x+1, y, i2b 1, 7))
      else
        if n > 0 then xl (x+1, y, b << 1, n-1)
        else (print b; xl (x+1, y, i2b 0, 7))
    else begin
      print (b << n);
      if (y < h-1) then xl (0, y+1, i2b 0, 8)
    end
in 
   printf ("P4\n%i %i\n", @(h, w)); if h > 0 then xl (0, 0, i2b 0, 8)
end // end of [mandelbrot]

implement
main (argc, argv) = let
//
  val () = assertloc (argc >= 2)
  val i = int1_of_string argv.[1]
  val () = assert_errmsg_bool1 (i >= 2, "The input integer needs to be at least 2.\n")
//
in
  mandelbrot (i, i)
end // end of [main]

(* ****** ****** *)

(* end of [mandelbrot.dats] *)
