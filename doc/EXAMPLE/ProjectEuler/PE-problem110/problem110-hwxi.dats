//
// ProjectEuler: Problem 110
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

staload _(*anon*) = "prelude/DATS/array0.dats"

(* ****** ****** *)

(*
primes = 2,3,5,7,11,13,17,19,23,19,31,37,41,43,47,...
*)

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

fun searchPrime
  {n:int | n >= 2} (n: int n): intGte 2 =
  if isprime (n) then n else searchPrime (n+1)
// end of [searchPrime]

(* ****** ****** *)

// for storing the first 20 primes
val P20 = array0_make_elt<int> (20, 0)

fun P20_print () = let
  var i: natLte 20 = 0 in
  for (i := 0; i < 20; i := i+1) printf ("P20[%i] = %i\n", @(i, P20[i]))
end // end of [P20_print]

val () = let
  var n: intGte 2 = 2
  var i: natLte 20 = 0
in
  for (i := 0; i < 20; i := i+1) let
    val () = n := searchPrime (n)
    val () = P20[i] := n; val () = n := n+1
  in
    // nothing
  end // end of [for]
end // end of [val]
(*
val () = P20_print ()
*)

(* ****** ****** *)

fun log (b: int, x: double): int = let
  fun loop (b: int, x: double, res: int): int =
    if x <= 1.0 then res else loop (b, x/b, res+1)
in
  loop (b, x, 0)
end // end of [log]

(* ****** ****** *)

fun search
  (s0: int, bound: double): ullint = let
  fun aux (
      i: int, n: int, pmin: int, fst: int, bound: double, res: ullint
    ) :<cloref1> ullint =
    if i <= n then let
      val res1 = search (s0+1, bound / (2*i + 1))
      val res2 = (ullint_of)fst * res1
      val res = (if res > 0ULL then min (res, res2) else res2): ullint
    in
      aux (i+1, n, pmin, pmin * fst, bound, res)
    end else res // end of [if]
  // end of [aux]
in
  if bound > 1.0 then let
    val pmin = P20[s0]
    val m = log (3, bound)
    val pmax = P20[s0 + m]
    val n = log (pmin, (double_of)pmax)
    val n = 1 + max (n, 3)
  in
    aux (1, n, pmin, pmin, bound, 0ULL)
  end else 1ULL
end // end of [search]

(* ****** ****** *)

#define _4M 4000000

implement
main () = () where {
  val ans = search (0, (double_of)(2*_4M-1))
  val () = assert_errmsg (ans = 9350130049860600ULL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem110-hwxi.dats] *)
