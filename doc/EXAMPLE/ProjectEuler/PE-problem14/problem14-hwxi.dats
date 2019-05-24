//
// ProjectEuler: Problem 14
// Finding the longest chain using a starting number below 1M
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

#define N 1000000
val theTable = array_make_elt<int> (N, ~1)
val () = theTable[1] := 0

(* ****** ****** *)

fun eval
  (n: &mpz_vt, c: int): int = let
  var saved: int = ~1
  val () = if mpz_cmp (n, N) < 0 then let
    val n1 = mpz_get_int (n)
    val [n:int] n1 = int1_of_int (n1)
    prval () = __assert () where {
      extern prfun __assert (): [0 <= n; n < N] void
    }
  in
    saved := theTable[n1]
  end // end of [val]
in
  if saved >= 0 then c + saved
  else if mpz_even_p (n) then let
    val _r = mpz_fdiv_q (n, 2UL) in eval (n, c+1)
  end else let
    val () = mpz_mul (n, 3UL); val () = mpz_add (n, 1UL)
  in
    eval (n, c+1)
  end // end of [if]
end // end of [eval]

(* ****** ****** *)

implement main () = () where {
  var imax: int = 0
  var cmax: int = 0
  var i: int // unintialized
  var x: mpz_vt; val () = mpz_init (x)
  val () = for*
    {i:int | i >= 2} (i: int i) =>
    (i := 2; i < N; i := i+1) let
    val () = mpz_set_ulint (x, (ulint_of)i)
    val c = eval (x, 0)
    val () = theTable[i] := c
  in
    if :(i: int i) => c > cmax then (imax := i; cmax := c)
  end // end of [val]
  val () = mpz_clear (x)
  val ans = imax
  val () = assert_errmsg (ans = 837799, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem14-hwxi.dats] *)
