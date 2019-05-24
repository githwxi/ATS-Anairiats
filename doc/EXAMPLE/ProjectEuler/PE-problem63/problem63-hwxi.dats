//
// ProjectEuler: Problem 63
// How many n-digit numbers are also the nth powers of (a single digit)?
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)

#define EPSILON 1E-6

implement main () = () where {
//
  val ans = loop (1.0, 1, 0) where {
    fun loop (x: double, n: int, ans: int): int = let
      val e = 1.0 / n
      val r = floor (pow (x, e) - EPSILON)
      val diff = int_of (9 - r)
(*
      val () = (print "loop: n = "; print n; print_newline ())
      val () = (print "loop: diff = "; print diff; print_newline ())
*)
    in
      if diff > 0 then loop (10 * x, n+1, ans + diff) else ans
    end // end of [loop]
  } // end of [val]
//
  val () = assert_errmsg (ans = 49, #LOCATION)
  val () = (print ("ans = "); print ans; print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [problem63-hwxi.dats] *)
