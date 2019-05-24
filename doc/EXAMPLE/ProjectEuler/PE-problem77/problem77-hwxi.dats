//
// ProjectEuler: Problem 77
// Find the first number which has more than 5000 ways in which
// it can be written as the sum of the at least two primes
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// f (n, k) = the number of ways in which n can be written as the sum of
// two or more primes >= k
//
// f (n, k) = 0 if n < 0
// f (n, k) = 1 if n = 0
// f (n, 0) = 0 if n > 0
// f (n, k) = f (n, k-1) if k is not a prime
// f (n, k) = f (n-k, k) + f (n, k-1) if n is a prime
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

fun isprime (n: int): bool = let
  val r = int_of (sqrt (n + 0.5))
  fun loop (p: int):<cloref1> bool =
    if p <= r then
      (if (n mod p > 0) then loop (p+1) else false)
    else true
  // end of [loop]
in
  if n >= 2 then loop (2) else false
end // end of [isprime]

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/matrix.dats"

(* ****** ****** *)

#define N 100
#define N1 %(N+1)
val theTable = matrix_make_elt<int> (N1, N, ~1) // ~1 is a placeholder

(* ****** ****** *)

fun f {n:int;k:nat | n < N1; k < N} .<max(n,0)+k>. (
    n: int n, k: int k
  ) : int =
  if n < 0 then 0
  else if n = 0 then 1
  else if k = 0 then 0
  else let
    val res = theTable[n, N, k]
  in
    if res >= 0 then res
    else let
      val res = (if isprime (k)
        then f (n-k, k) + f (n, k-1) else f (n, k-1)
      ) : int // end of [if]
      val () = theTable[n, N, k] := res
    in
      res
    end // end of [if]
  end // end of [if]
// end of [f]

val () = assert_errmsg (f (10, 9) = 5, #LOCATION)

(* ****** ****** *)

implement
main () = () where {
  fun loop (n: intGte 10): int =
    if n <= N then let
      val res = f (n, n-1) in if res > 5000 then n else loop (n+1)
    end else exit (1)
  val ans = loop (10)
//  val () = assert_errmsg (ans = 190569291LL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem77-hwxi.dats] *)
