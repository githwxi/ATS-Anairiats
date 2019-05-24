//
// ProjectEuler: Problem 29
// How many distinct numbers in a^b for 2 <= a,b <= 100
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun pow
  (a: uint, b: uint): string = let
  var res: mpz_vt; val () = mpz_init_set (res, a)
  val () = mpz_pow_ui (res, (ulint_of)b)
  val str = mpz_get_str (10, res)
  val () = mpz_clear (res)
in
  string_of_strptr (str)
end // end of [pow]

(* ****** ****** *)

staload M = "libats/SATS/funmap_avltree.sats"
staload _(*anon*) = "libats/DATS/funmap_avltree.dats"

(* ****** ****** *)

implement main () = () where {
  typedef key = string
  fn cmp (x1: key, x2: key):<cloref> Sgn = compare (x1, x2)
  typedef map = $M.map (string, int)
  fun loop2
    (a: uint, b: uint, m: &map): void =
    if b <= 100U then let
      val str = pow (a, b)
      val _ = $M.funmap_insert (m, str, 0, cmp)
    in
      loop2 (a, b+1U, m)
    end // end of [if]
  // end of [loop2]
  fun loop1 (a: uint, m: &map): void =
    if a <= 100U then let
      val () = loop2 (a, 2U, m) in loop1 (a+1U, m)
    end // end of [if]
  // end of [loop1]
  var m0: map = $M.funmap_make_nil ()
  val () = loop1 (2U, m0)
  val ans = $M.funmap_size (m0)
  val () = assert_errmsg (ans = 9183, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem29-hwxi.dats] *)
