//
// ProjectEuler: Problem 65
// Finding the digitsum of the numerator of
// the 100th convergent of the continued fraction of e
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

val theFracLst: stream (int) = let
  fun genLst (n: int):<!laz> stream (int) =
    $delay (stream_cons (1, $delay (stream_cons (2*n, $delay (stream_cons (1, genLst (n+1)))))))
in
  genLst (1)
end // end of [val]

(* ****** ****** *)

fun compFrac {i,n:nat | i <= n} .<n-i>.
  (res: &mpq_vt, x: int, xs: stream (int), i: int i, n: int n): void = let
  val x = (uint_of)x
in
  if i < n then let
    val- stream_cons (x1, xs1) = !xs
    val () = compFrac (res, x1, xs1, i+1, n)
    val () = mpq_inv (res)
    val () = mpq_incby (res, (ulint_of)x, 1UL)
  in
    // nothing
  end else let
    val () = mpq_set (res, (ulint_of)x, 1UL) in (*nothing*)
  end // end of[ if]
end // end of [compFrac]

(* ****** ****** *)

implement main () = () where {
  var res: mpq_vt; val () = mpq_init (res)
//
  val () = compFrac (res, 2, theFracLst, 1, 10)
  val (pf, fpf | p) = mpq_numref (res)
  val ans = digitsum (!p)
  prval () = fpf (pf)
  val () = (print ("res = "); print res; print_newline ())
  val () = (print ("ans(10) = "); print ans; print_newline ())
//
  val () = compFrac (res, 2, theFracLst, 1, 100)
  val (pf, fpf | p) = mpq_numref (res)
  val ans = digitsum (!p)
  prval () = fpf (pf)
  val () = mpq_clear (res)
  val () = assert_errmsg (ans = 272, #LOCATION)
  val () = (print ("ans(100) = "); print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem65-hwxi.dats] *)
