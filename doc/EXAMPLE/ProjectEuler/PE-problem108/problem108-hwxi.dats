//
// ProjectEuler: Problem 108
// Finding the number of soutions to 1/x+1/y = 1/n, which n is chosen
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

//
// HX: for each n, the answer is the number of divisors of n^2 that are
// less than or equal to n
//

(* ****** ****** *)

fun n2divisor
  (n: int): int = let
  val n1 = ullint_of (n)
  val n2 = n1 * n1
  fun loop (i: int, sum: int):<cloref1> int =
    if i <= n then
      (if n2 mod (ullint_of)i = 0ULL then loop (i+1, sum+1) else loop (i+1, sum))
    else sum // end of [loop]
  // end of [loop]
in
  loop (1, 0)
end // end of [n2divisor]

(* ****** ****** *)

#define N 1000
#define DELTA %(2*3*5*7) // HX: this is kind of cheating :) see PE-problem110

fun search
  (x: int): int = let
  val n = n2divisor (x)
(*
  val () = (print "x = "; print x; print_newline ())
  val () = (print "n = "; print n; print_newline ())
*)
in
  if n > N then x else search (x+DELTA)
end // end of [search]

(* ****** ****** *)

implement
main () = () where {
  val ans = search (0)
  val () = assert_errmsg (ans=180180, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem108-hwxi.dats] *)
