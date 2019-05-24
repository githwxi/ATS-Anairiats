//
// ProjectEuler: Problem 162
// How many numbers are there that are at most 16 hexdigit-long and these hexdigits
// contain at least one occurrence of each of 0, 1, and A.
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

#define NDIGIT 16

(* ****** ****** *)
// Suppose we have N letters and each word is sequence of these letters.
//
// f0 (n) = the number of words of length at most n
// f1 (n) = the number of words of length at most n containing 1 given letter
// f2 (n) = the number of words of length at most n containing 2 given distinct letters
// f3 (n) = the number of words of length at most n containing 3 given distinct letters
//
// f0(n) = 1+N^1+...+N^n = (N^(n+1)-1)/(N-1)
// f1(n) = f0(n-1) + (N-1)*f1(n-1)
// f2(n) = 2*f1(n-1) + (N-2)*f2(n-1)
// f3(n) = 3*f2(n-1) + (N-3)*f3(n-1)
//
// The answer = 2*f2(15) + 13*f3(15) // leading 0's are not allowed

(* ****** ****** *)

fun f0 {n:nat}
  (n: int n, res: &mpz_vt): void = let
  val () = mpz_set_ulint (res, ulint_of(NDIGIT))
  val () = mpz_pow_ui (res, (ulint_of)(n+1))
  val () = mpz_sub2_ulint (res, 1UL)
  val _r = mpz_fdiv_q (res, ulint_of(NDIGIT - 1))
in
  // nothing
end // end of [f0]

(* ****** ****** *)

fun f1 {n:nat}
  (n: int n, res: &mpz_vt): void =
  if n >= 1 then let
    val () = f1 (n-1, res)
    val () = mpz_mul (res, ulint_of(NDIGIT-1))
    var res2: mpz_vt; val () = mpz_init (res2)
    val () = f0 (n-1, res2)
    val () = mpz_add (res, res2)
    val () = mpz_clear (res2)
  in
    // nothing
  end else let
    val () = mpz_set (res, 0) in (*nothing*)
  end // end of [if]
// end of [f1]

(* ****** ****** *)

fun f2 {n:nat}
  (n: int n, res: &mpz_vt): void =
  if n >= 2 then let
    val () = f2 (n-1, res)
    val () = mpz_mul (res, ulint_of(NDIGIT-2))
    var res2: mpz_vt; val () = mpz_init (res2)
    val () = f1 (n-1, res2)
    val () = mpz_mul (res2, 2UL)
    val () = mpz_add (res, res2)
    val () = mpz_clear (res2)
  in
  end else let
    val () = mpz_set (res, 0) in (*nothing*)
  end // end of [if]
// end of [f2]

(* ****** ****** *)

fun f3 {n:nat}
  (n: int n, res: &mpz_vt): void =
  if n >= 3 then let
    val () = f3 (n-1, res)
    val () = mpz_mul (res, ulint_of(NDIGIT-3))
    var res2: mpz_vt; val () = mpz_init (res2)
    val () = f2 (n-1, res2)
    val () = mpz_mul (res2, 3UL)
    val () = mpz_add (res, res2)
    val () = mpz_clear (res2)
  in
  end else let
    val () = mpz_set (res, 0) in (*nothing*)
  end // end of [if]
// end of [f3]

(* ****** ****** *)

implement main () = let
  var res: mpz_vt; val () = mpz_init (res)
  val () = f2 (NDIGIT-1, res)
  val () = mpz_mul (res, 2UL)
  var res2: mpz_vt; val () = mpz_init (res2)
  val () = f3 (NDIGIT-1, res2)
  val () = mpz_mul (res2, ulint_of(NDIGIT-3))
  val () = mpz_add (res, res2)
  val ans = mpz_get_str (NDIGIT, res)
  val (pf_gc, pf | p) = strbuf_of_strptr (ans)
  val () = strbuf_toupper (!p)
  val ans = strptr_of_strbuf @(pf_gc, pf | p)
  val sgn =
    compare (__cast ans, "3D58725572C62302") where {
    extern castfn __cast {l:addr} (x: !strptr l):<> string
  } // end of [val]
  val () = assert_errmsg (sgn = 0, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
  val () = strptr_free (ans)
  val () = mpz_clear (res)
  val () = mpz_clear (res2)
in
  // nothing
end // end of [main]

(* ****** ****** *)

(* end of [problem162-hwxi.dats] *)
