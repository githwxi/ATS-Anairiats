//
// ProjectEuler: Problem 73
// Calculating the number of proper reduced fractions n/d
// between 1/3 and 1/2
//

(* ****** ****** *)
//
// Author Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

fun test
  (d: int): int = res where {
  val n0 = (d+2)/3; val n1 = d/2
  fun loop (d: int, n0: int, n1: int, res: &int): void =
    if n0 <= n1 then let
      val () = if gcd (n0, d) = 1 then res := res + 1
    in
      loop (d, n0+1, n1, res)
    end // end of [if]
  // end of [loop]
  var res: int = 0
  val () = loop (d, n0, n1, res)
} // end of [test]

(* ****** ****** *)

#define DENOM 12000

implement
main (argc, argv) = () where {
  var cnt: int = 0
  var d: int // uninitialized
  val () = for
    (d := 4; d <= DENOM; d := d+1) cnt := cnt + test (d)
  // end of [val]
  val ans = cnt
  val () = assert_errmsg (ans = 7295372, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem73-hwxi.dats] *)
