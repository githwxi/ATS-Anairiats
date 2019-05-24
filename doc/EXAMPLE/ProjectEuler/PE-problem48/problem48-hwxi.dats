//
// ProjectEuler: Problem 48
// Finding the last 10 digits of (1^1+2^2+...+1000^1000)
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
  macdef N = 10000000000ULL
  val ans = loop (1U, 1000U, 0ULL) where {
    fun loop (l: uint, r: uint, sum: ullint): ullint =
      if l <= r then let
        var x: mpz_vt
        val () = mpz_init_set (x, l)
        val () = mpz_pow_ui (x, (ulint_of)l)
        var d: mpz_vt; val () = mpz_init_set (d, 10E10)
        val () = mpz_mod (x, d)
        val rx = mpz_get_double (x)
        val () = mpz_clear (x); val () = mpz_clear (d)
        val sum = sum + (ullint_of_double)rx
      in
        loop (l+1U, r, sum)
      end else sum
    // end of [loop]
  } // end of [val]
  val ans = ans mod N
  val () = assert_errmsg (ans = 9110846700ULL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem48-hwxi.dats] *)
