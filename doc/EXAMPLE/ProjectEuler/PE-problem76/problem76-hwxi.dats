//
// ProjectEuler: Problem 76
// Find the number of ways in which 100 can be written as
// the sum of the at least two positive integers
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// f (n, k) = the number of ways in which n can be written as the sum of
// two or more integers >= k
//
// f (n, k) = 0 if n < 0
// f (n, k) = 1 if n = 0
// f (n, 0) = 0 if n > 0
// f (n, k) = f (n-k, k) + f (n, k-1)
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/matrix.dats"

(* ****** ****** *)

#define N 101
#define N1 %(N+1)
val theTable = matrix_make_elt<llint> (N1, N, ~1LL) // ~1 is a placeholder

(* ****** ****** *)

fun f {n:int;k:nat | n < N1; k < N} .<max(n,0)+k>. (
    n: int n, k: int k
  ) : llint =
  if n < 0 then 0LL
  else if n = 0 then 1LL
  else if k = 0 then 0LL
  else let
    val res = theTable[n, N, k]
  in
    if res >= 0LL then res
    else let
      val res = f (n-k, k) + f (n, k-1)
      val () = theTable[n, N, k] := res
    in
      res
    end // end of [if]
  end // end of [if]
// end of [f]

val () = assert_errmsg (f(5,4) = 6LL, #LOCATION)

(* ****** ****** *)

implement
main () = () where {
  val ans = f (100, 99)
  val () = assert_errmsg (ans = 190569291LL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem76-hwxi.dats] *)
