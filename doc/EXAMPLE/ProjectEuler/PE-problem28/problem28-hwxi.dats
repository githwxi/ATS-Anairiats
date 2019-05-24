//
// ProjectEuler: Problem 28
// Finding the sum of both diagnals in a 1001x1001 spiral
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)
//
// f(1) = 1
// f(3) = f(1) + 9 + 7 + 5 + 3 = 25
// f(5) = f(3) + 25 + 21 + 17 + 13 = 101
// g(k) = f(2k+1) = g(k-1) + 4*(2k+1)^2 - 6*k
//
(* ****** ****** *)

fun g (k: int): int =
 if k > 0 then g (k-1) + 4 * square (2*k+1) - 12*k else 1
// end of [g]

(* ****** ****** *)

implement
main () = () where {
  val ans = g (2)
  val () = assert_errmsg (ans = 101, #LOCATION)
  val ans = g (500)
  val () = assert_errmsg (ans = 669171001, #LOCATION)
  val () = printf ("ans = %i\n", @(ans))
} // end of [main]

(* ****** ****** *)

(* end of [problem28-hwxi.dats] *)
