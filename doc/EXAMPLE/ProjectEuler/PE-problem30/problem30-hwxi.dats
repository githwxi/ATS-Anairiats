//
// ProjectEuler: Problem 30
// Finding all the numbers that equal
// the sum of the fifth powers of their digits.
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

fn p5 (n: int): int = let
  val n2 = n * n in (n2 * n2) * n
end // end of [p5]

(* ****** ****** *)

fun test (x: int): bool = let
  fun loop (x: int, sum: int): int =
    if x > 0 then let
      val r = x mod 10 in loop (x/10, sum + p5(r))
    end else sum // end of [if]
  // end of [loop]
in
  x = loop (x, 0)
end // end of [test]

(* ****** ****** *)

implement main () = () where {
  #define N 1000000
  fun loop (n: int, sum: int): int =
    if n < N then
      (if test (n) then loop (n+1, sum + n) else loop (n+1, sum))
    else sum // end of [if]
  // end of [loop]
  val ans = loop (10, 0)
  val () = assert_errmsg (ans = 443839, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem30-hwxi.dats] *)
