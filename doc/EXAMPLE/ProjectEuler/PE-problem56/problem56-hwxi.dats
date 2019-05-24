//
// ProjectEuler: Problem 56
// Finding the maximal digitsum of the numbers of the form a^b for a,b < 100
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

// HX: [x] is set to 0 after the call
fun digitsum
  (x: &mpz_vt): ulint = let
  fun loop (x: &mpz_vt, sum: ulint): ulint = let
    val sgn = mpz_cmp (x, 0UL)
  in
    if sgn > 0 then let
      val r = mpz_fdiv_q (x, 10UL) in loop (x, sum + r)
    end else sum
  end // end of [loop]
in
  loop (x, 0UL)
end // end of [digitsum]

(* ****** ****** *)

fun loop1 (
    a: uint, x: &mpz_vt, x1: &mpz_vt
  , j: uint, n: uint, max: &ulint, im: &uint, jm: &uint
  ) : void =
  if j < n then let
    val () = mpz_mul (x, (ulint_of)a)
    val () = mpz_set (x1, x)
    val sum = digitsum (x1)
    val () = if (sum > max) then (max := sum; im := a; jm := j)
  in
    loop1 (a, x, x1, j+1U, n, max, im, jm)
  end else ()
// end of [loop1]

fun loop2 (
    x: &mpz_vt, x1: &mpz_vt
  , i: uint, n: uint, max: &ulint, im: &uint, jm: &uint
  ) : void =
  if i < n then let
    val () = mpz_set (x, 1)
    val () = loop1 (i, x, x1, 1U, n, max, im, jm)
  in
    loop2 (x, x1, i+1U, n, max, im, jm)
  end else ()
// end of [loop2]

(* ****** ****** *)

implement main () = () where {
//
  var max: ulint = 0UL
  var im: uint = 0U and jm: uint = 0U
  var x: mpz_vt and x1: mpz_vt
  val () = mpz_init (x) and () = mpz_init (x1)
  val () = loop2 (x, x1, 1U, 100U, max, im, jm)
  val () = mpz_clear (x) and () = mpz_clear (x1)
  val ans = max
//
  val () = (printf ("ans(%u^%u) = ", @(im, jm)); print ans; print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [problem56-hwxi.dats] *)
