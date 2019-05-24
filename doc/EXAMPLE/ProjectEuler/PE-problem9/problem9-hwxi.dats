//
// ProjectEuler: Problem 9
// Finding the only Pythagorean triplet (a,b,c) such that a+b+c=1000
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)
//
// HX: here is the reasoning:
//
// gcd(p,q) = 1
// a = k(2pq)
// b = k(p^2 - q^2) // p >= q
// c = k(p^2 + q^2)
// a+b+c = k(2p(p+q)) = 1000 = (2^3)(5^3)
//
// kp(p+q) = (2^2)(5^3)
// k = 25
// p(p+q) = 40 => p = 4 and q = 1
//
implement main () = () where {
  val a = 200
  val b = 375
  val c = 425
  val () = assert (a*a + b*b = c*c)
  val () = assert (a + b + c = 1000)
  val () = printf ("abc = %i\n", @(a*b*c))
} // end of [main]

(* ****** ****** *)

(* end of [problem9-hwxi.dats] *)
