//
// ProjectEuler: Problem 16
// Finding the sum of all the digits of 2^1000
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun digitsum
  (x: &mpz_vt): int = let
  val str = mpz_get_str (10, x)
  val @(pf_gc, pf | p) = strbuf_of_strptr (str)
  val n = strbuf_length (!p)
  val sum = loop (!p, n, 0, 0) where {
    fun loop {m,n:nat} {i:nat | i <= n}
      (buf: &strbuf (m, n), n: size_t n, i: size_t i, sum: int): int =
      if i < n then loop (buf, n, i+1, sum+(buf[i]-'0')) else sum
    // end of [loop]
  } // end of [sum]
  val str = strptr_of_strbuf @(pf_gc, pf | p)
  val () = strptr_free (str)
in
  sum
end // end of [digitsum]

(* ****** ****** *)

implement main () = () where {
//
  var p15: mpz_vt; val () = mpz_init_set (p15, 2)
  val () = mpz_pow_ui (p15, 15UL)
  val sum15 = digitsum (p15)
  val () = mpz_clear (p15)
  val () = assert_errmsg (sum15 = 26, #LOCATION)
//
  var p1000: mpz_vt; val () = mpz_init_set (p1000, 2)
  val () = mpz_pow_ui (p1000, 1000UL)
  val sum1000 = digitsum (p1000)
  val () = mpz_clear (p1000)
  val () = assert_errmsg (sum1000 = 1366, #LOCATION)
  val () = (print "the sum of all the digits of 2^1000 is "; print sum1000; print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [problem16-hwxi.dats] *)
