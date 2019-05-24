//
// ProjectEuler: Problem 78
// Find the number of ways in which a given
// natural number can be represented as the
// sum of some natural numbers
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX:
// let g(x) = (1/(1-x))(1/(1-x^2))(1/(1-x^3))...
// then the coefficient of x^n in g(x) is the p(n)
// 1/g(x) = 1-x-x^2+x^5+x^7-x^12-x^15+...
// Let q(n) = n(3n-1)/2 // q(0) = 0; q(1) = 1; q(-1) = 2; q(2) = 5; q(-2) = 7
// 1/g(x) = Sigma_n (-1)^n x^{q(n)} // Euler's Pentagonal number theorem
//
// So p(n) = p(n-1) + p(n-2) - p(n-5) - p(n-7) + p (n-12) + p (n-15) - ...
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

fun pentagon (n: int): int = n * (3*n-1) / 2

(* ****** ****** *)

#define N 1000000 // big enough?
val theTable = array_make_elt<int> (N, ~1)

(* ****** ****** *)

#define _1M 1000000

fun p (n: int): int = let
//  val () = (print "p: n = "; print n; print_newline ())
  fun loop {n:nat} (
      n: int n, k: int, sgn: int, res: int
    ) : int = let
(*
    val () = (print "p: loop: k = "; print k; print_newline ())
*)
    val pk = pentagon (k)
    val pk1 = pk + k // = pentagon (~k)
  in
    if n >= pk then let
      val res = res + sgn * (p (n-pk) + p (n-pk1))
      val res = res mod _1M
    in
      loop (n, k+1, ~sgn, res)
    end else res
  end // end of [loop]
  val n = int1_of_int (n)
in
  if n = 0 then 1
  else if n > 0 then let
    val res = (if n < N then theTable[n] else 0): int
  in
    if res >= 0 then res
    else let
      val res = loop (n, 1, 1, 0)
      val res = if res >= 0 then res else _1M+res
      val () = if n < N then theTable[n] := res
    in
      res
    end // end of [if]
  end else 0 // end of [if]
end // end of [p]

(* ****** ****** *)

val () = assert_errmsg (p(5) = 7, #LOCATION)

(* ****** ****** *)

implement
main () = () where {
  var n: int = 0
  val () = while (true) let
(*
    val () = printf ("p(%i) = %i\n", @(n, p(n)))
*)
    val () = if p(n) = 0 then break
  in
    n := n + 1
  end // end of [val]
  val ans = n
  val () = assert_errmsg (ans = 55374, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem78-hwxi.dats] *)
