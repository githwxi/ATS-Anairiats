//
// ProjectEuler: Problem 46
// Finding the first 4 consecutive numbers such that each of these
// numbers can be written in the form p1^n1 * p2^n2 * p3^n3 * p4^n4
// for some primes p1 < p2 < p3 < p4, wheren n1,n2,n3,n4 are positive.
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

fun nprime
  (x: int, p: int): int =
  if x > 1 then
    if p * p <= x then
      (if x mod p = 0 then nprime1 (x / p, p) else nprime (x, p+1))
    else 1 // end of [if]
  else 0 (* end of [if] *)
// end of [nprime]

and nprime1 (x: int, p: int): int =
  if x mod p = 0 then nprime1 (x / p, p) else 1 + nprime (x, p+1)
// end of [nprime1]

(* ****** ****** *)

fun search (x: int, n: int): int =
  if nprime (x, 2) = n then search1 (x, n, x+1, n-1) else search (x+1, n)
// end of [search]

and search1 (x: int, n: int, x1: int, n1: int): int =
  if n1 > 0 then
    if nprime (x1, 2) = n then search1 (x, n, x1+1, n1-1) else search (x+1, n)
  else x // end of [if]
// end of [search1]

(* ****** ****** *)

implement
main () = () where {
  val ans = search (2, 2)
  val () = assert (ans = 14)
  val ans = search (2, 3)
  val () = assert (ans = 644)
  val ans = search (2, 4)
  val () = assert (ans = 134043)
  val () = (print "ans(4) = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem46-hwxi.dats] *)
