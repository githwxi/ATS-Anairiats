//
// ProjectEuler: Problem 55
// Finding the number of Lychrel numbers under 10 thousand
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun reverse
  (rx: &mpz_vt, x: &mpz_vt): void =
  if mpz_cmp (x, 0) > 0 then let
    val r = mpz_fdiv_q (x, 10UL)
    val () = mpz_mul (rx, 10UL); val () = mpz_add (rx, r)
  in
    reverse (rx, x)
  end // end of [if]
// end of [reverse]

(* ****** ****** *)

fun isLychrel
  (x0: int): bool = let
  var x: mpz_vt; val () = mpz_init_set (x, x0)
  var x1: mpz_vt; val () = mpz_init_set (x1, x)
  var rx: mpz_vt; val () = mpz_init_set (rx, 0)
  val () = reverse (rx, x1)
  val () = mpz_add (x, rx) // x = x + rev(x)
//
  fun loop (x: &mpz_vt, x1: &mpz_vt, rx: &mpz_vt, n: int): bool = let
    val () = mpz_set (x1, x)
    val () = mpz_set (rx, 0)
    val () = reverse (rx, x1)
(*
    val () = (print "isLychrel: loop: x = "; print x; print_newline ())
    val () = (print "isLychrel: loop: rx = "; print rx; print_newline ())
*)
  in
    if mpz_cmp (x, rx) = 0 then false else (
      if n < 50 then let
        val () = mpz_add (x, rx) in loop (x, x1, rx, n+1)
      end else true // true after 50 tests!
    ) // end of [if]
  end // end of [loop]
//
  val res = loop (x, x1, rx, 1)
  val () = mpz_clear (x)
  val () = mpz_clear (x1)
  val () = mpz_clear (rx)
in
  res
end // end of [isLychrel]

(* ****** ****** *)

val () = assert_errmsg (isLychrel 196, #LOCATION)
val () = assert_errmsg (isLychrel 4994, #LOCATION)

(* ****** ****** *)

implement main () = () where {
  var i: int = 0
  var cnt: int = 0
  val () = while (true) let
    val () = if i >= 10000 then break
    val () = if isLychrel (i) then cnt := cnt + 1
  in
    i := i + 1
  end // end of [val]
  val ans = cnt
  val () = assert_errmsg (ans = 249, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem55-hwxi.dats] *)
