//
// ProjectEuler: Problem 20
// Finding the sum of all the digits of 100!
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
  var f100: mpz_vt; val () = mpz_init (f100)
  val () = mpz_fac_ui (f100, 100UL)
  val sum100 = digitsum (f100)
  val () = mpz_clear (f100)
  val () = assert_errmsg (sum100 = 648, #LOCATION)
  val () = (print "the sum of all the digits of 100! is "; print sum100; print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [problem20-hwxi.dats] *)
