//
// ProjectEuler: Problem 69
// Finding the number n below 1M that maximizes the value n/phi(n),
// where phi is Euler's totient function
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Septemeber, 2010
//
(* ****** ****** *)
//
// HX: let p1, ..., pk be the list of distinct prime factors of n; then
// phi(n) = n*(1-1/p1)*...*(1-1/pk); so n/phi(n) = 1/(1-1/p1)...(1-1/pk)
// so maximizing n/phi(n) is equivalent to minimizing (1-1/p1)...(1-1/pk)
//
// The the answer to this question is 2*3*5*7*...*p where p is the largest
// prime number satisfying 2*3*5*7*...*p <= 1M
//
(* ****** ****** *)

fun isqrt
  (x: uint): uint =
  if x >= 2U then let
    val x4 = x / 4U
    val r2 = isqrt (x4)
    val r = r2 + r2
    val r_1 = r + 1U
  in
    if r_1 * r_1 > x then r else r_1
  end else x 
// end of [isqrt]

(* ****** ****** *)

fun isprime
  {n:int | n >= 2}
  (n: int n): bool = let
  val u = uint_of_int (n)
  val r = isqrt (u)
(*
  val () = (print "u = "; print u; print_newline ())
  val () = (print "r = "; print r; print_newline ())
*)
  fun loop (p: uint):<cloref1> bool =
    if p <= r then
      (if (u mod p > 0U) then loop (p+1U) else false)
    else true
  // end of [loop]
in
  loop (2U)
end // end of [isprime]

(* ****** ****** *)

#define _1M 1000000

fun search {p:int | p >= 2}
  (p: int p, res: int): int =
  if isprime (p) then let
    val res1 = res * p in if res1 <= _1M then search (p+1, res1) else res
  end else search (p+1, res)
// end of [search]

(* ****** ****** *)

implement
main () = () where {
  val ans = search (2, 1)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem69-hwxi.dats] *)
