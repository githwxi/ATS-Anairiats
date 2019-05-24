//
// ProjectEuler: Problem 1
// Finding the sum of all numbers below 1000 that is a multiple of 3 or 5
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December, 2010
//
(* ****** ****** *)

implement main () = () where {
  #define N 1000
  val ans = loop (0, 0) where {
    fun loop (i: int, res: int): int = 
      if i < N then
        loop (i+1, if (i mod 3 = 0 orelse i mod 5 = 0) then res+i else res)
      else res // end of [if]
  } // end of [val]
  val () = (
    printf ("The sum of all the natural numbers < %i that are multiples of 3 or 5 = ", @(N));
    print ans;
    print_newline ()
  ) // end of [val]
} // end of [main]

(* ****** ****** *)

(* end of [problem1-hwxi.dats] *)
