//
// ProjectEuler: Problem 97
// Finding the last 10 digits of 28433 * 2^7830457 + 1
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

implement
main () = () where {
  val N = 1E10
  var m: mpz_vt
  val () = mpz_init_set (m, N)
  var x: mpz_vt; val () = mpz_init (x)
  var b: mpz_vt; val () = mpz_init_set (b, 2UL)
  val () = mpz_powm (x, b, 7830457UL(*exp*), m)
  val () = mpz_mul (x, 28433UL)
  val () = mpz_add (x, 1UL)
  val () = mpz_mod (x, m)
  val ans = mpz_get_double (x)
  val () = mpz_clear (m)
  val () = mpz_clear (x)
  val () = mpz_clear (b)
  val () = assert_errmsg (ans = 8739992577.0, #LOCATION)
  val () = (print "ans = "; printf ("%10.0f", @(ans)); print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem97-hwxi.dats] *)
