//
// ProjectEuler: Problem 25
// Finding the first Fibonacci term containing at least 1000 digits
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//
(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun p25 
  (f1: &mpz_vt, f2: &mpz_vt, N: &mpz_vt, n: int): int = let
  val sgn = mpz_cmp (f2, N)
in
  if sgn < 0 then let
    val () = mpz_add (f1, f2) in p25 (f2, f1, N, n+1)
  end else n
end // end of [p25]

(* ****** ****** *)

implement main () = () where {
//
  var f1: mpz_vt; val () = mpz_init_set (f1, 1)
  var f2: mpz_vt; val () = mpz_init_set (f2, 1)
  var N: mpz_vt; val () = mpz_init_set (N, 10); val () = mpz_pow_ui (N, 999UL)
  val n1000 = p25 (f1, f2, N, 2)
  val () = mpz_clear (f1) and () = mpz_clear (f2)  
  val () = mpz_clear (N)
  val () = assert_errmsg (n1000 = 4782, #LOCATION)
  val () = printf ("F(%i) is the first Fibonacci term containing at least 1000 digits.\n", @(n1000))
//
} // end of [main]

(* ****** ****** *)

(* end of [problem25-hwxi.dats] *)
