//
// ProjectEuler: Problem 57
// Investigate the expansion of the continued fraction
// for the square root of 2
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun count {n:nat}
  (n: int n): int = let
  fun loop
    {n,i:nat | i <= n} .<n-i>.
    (f: &mpq_vt, x: &mpz_vt, n: int n, i: int i, c: int): int =
    if i < n then let
      val () = mpq_incby (f, 2UL, 1UL)
      val () = mpq_inv (f)
      val (pf_num, fpf_num | p_num) = mpq_numref (f)
      val (pf_den, fpf_den | p_den) = mpq_denref (f)
      val () = mpz_set (x, !p_num)
      prval () = fpf_num (pf_num)
      val () = mpz_add (x, !p_den)
      val str = mpz_get_str (10, x)
      val sz_x = strptr_length (str)
      val () = strptr_free (str)
      val str = mpz_get_str (10, !p_den)
      val sz_den = strptr_length (str)
      val () = strptr_free (str)
      prval () = fpf_den (pf_den)
    in
      loop (f, x, n, i+1, c + (int_of_size)sz_x-(int_of_size)sz_den)
    end else c // end of [if]
  // end of [loop]
  var f: mpq_vt; val () = mpq_init (f)
  val () = mpq_set_ui (f, 0UL, 1UL)
  var x: mpz_vt; val () = mpz_init (x)
  val res = loop (f, x, n, 0, 0)
  val () = mpq_clear (f)
  val () = mpz_clear (x)
in
  res (* return value *)
end // end of [count]

(* ****** ****** *)

implement main () = () where {
  val ans = count (8)
  val () = (print "ans(8) = "; print ans; print_newline ())
  val ans = count (1000)
  val () = assert_errmsg (ans = 153, #LOCATION)
  val () = (print "ans(1000) = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem57-hwxi.dats] *)
