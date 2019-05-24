//
// ProjectEuler: Problem 15
// Starting from the top left corner of a 20x20 grid, how many
// routes are there to the bottom right corner?
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)
//
// HX: the answer = choose (20/40)
//
implement main () = () where {
  var res: mpz_vt; val () = mpz_init (res)
  val () = mpz_bin_uiui (res, ulint_of(20+20), ulint_of(20))
  val ans = mpz_get_double (res)
  val () = assert_errmsg (ans = 137846528820.0, #LOCATION)
  val () = (print "ans = "; printf ("%.0f", @(ans)); print_newline ())
  val () = mpz_clear (res)
} // end of [main]

(* ****** ****** *)

(* end of [problem15-hwxi.dats] *)
