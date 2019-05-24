//
// ProjectEuler: Problem 5
// Finding the lcm of (1, ..., 20)
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fn nlcm {n:nat}
  (n: int n): ulint = res where {
  fun loop {i:nat} .<n+1 nsub i>.
    (i: int i, lcm: &mpz_vt):<cloref1> void =
    if i <= n then
      (mpz_lcm (lcm, (ulint_of)i); loop (i+1, lcm))
  // end of [loop]
  var lcm: mpz_vt; val () = mpz_init_set (lcm, 1)
  val () = loop (2, lcm)
  val res = mpz_get_ulint (lcm)
  val () = mpz_clear (lcm)
} // end of [nlcm]

(* ****** ****** *)

implement main () = () where {
  val ans = nlcm (20)
  val () = assert_errmsg (ans = 232792560UL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem5-hwxi.dats] *)
