//
// ProjectEuler: Problem 2
// Finding the sum of all even Fibonacci numbers not exceeding 4M
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun loop (
    N: ulint, i: ulint, ifib: &mpz_vt, sum: &mpz_vt
  ) : void = let
  val () = mpz_fib_ui (ifib, i)
(*
  val () = (print "i = "; print i; print_newline ())
  val () = (print "ifib = "; print ifib; print_newline ())
*)
  val sgn = mpz_cmp_ulint (ifib, N)
in
  if sgn < 0 then let
    val () = if mpz_even_p (ifib) then mpz_add (sum, ifib)
  in
    loop (N, i+1UL, ifib, sum)
  end else ()
end // end of [loop]

(* ****** ****** *)

implement main () = () where {
  var ifib: mpz_vt; val () = mpz_init (ifib)
  var sum: mpz_vt; val () = mpz_init_set (sum, 0UL)
  macdef N = 4000000UL
  val () = loop (N, 2UL, ifib, sum) // starting from the 2nd Fib number
  val () = assert_errmsg (mpz_get_ulint (sum) = 4613732UL, #LOCATION)
  val () = println! ("The sum of all even Fibonacci numbers < 4 million = ", sum)
  val () = mpz_clear (ifib)
  val () = mpz_clear (sum)
} // end of [main]

(* ****** ****** *)

(* end of [problem2-hwxi.dats] *)
