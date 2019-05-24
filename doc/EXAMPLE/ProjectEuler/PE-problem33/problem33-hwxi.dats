//
// ProjectEuler: Problem 33
// Discovering all the fractions with an unorthodox cancelling method
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun test (i: int, j: int, k: int): bool = (i*10 + k) * j = (10*k+j) * i

(* ****** ****** *)

implement main () = () where {
  var nump: int = 1 and denp: int = 1
  var i: int = 0 and j: int = 0 and k: int = 0
  val () =
    for (i := 0; i <= 8; i := i+1)
    for (j := i+1; j <= 9; j := j+1)
      for (k := 1; k <= 9; k := k+1)
        if test (i, j, k) then let
          val () = nump := (10 * i + k) * nump
          val () = denp := (10 * k + j) * denp
        in
          // nothing
        end // end of [if]
      // end of [for]
    // end of [for;for]
  // end of [val]
  val x = gcd (nump, denp)
  val ans = denp / x
  val () = assert_errmsg (ans = 100, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem33-hwxi.dats] *)
