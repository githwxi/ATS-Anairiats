//
// ProjectEuler: Problem 66
// Investigating the Diophantine equation x^2-Dy^2 = 1
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)

fun isqrt
  (x: int): int = int_of(sqrt (x+0.5))
fun issquare (x: int): bool = let
  val x2 = isqrt (x) in x2 * x2 = x
end // end of [issquare]

fun issquarefree
  (x: int): bool = let
  val x2 = isqrt (x)
  fun loop (p: int):<cloref1> bool =
    if p <= x2 then (
      if x mod p = 0 then let
        val x1 = x / p in
        if x1 mod p = 0 then false else loop (p+1)
      end else loop (p+1)
    ) else true
  // end of [loop]
in
  if x >= 2 then loop (2) else false
end // end of [issquarefree]

(* ****** ****** *)

(*

//
// HX-2010-09-27: this naive method cannot get far enough
//

(* ****** ****** *)

//
// HX: assume: gcd (u, v) = 1
// u * v = D y^2 ?
//
fun test (
    D: int, u: int, v: int
  ) : bool = let
  val ugcd = gcd (D, u)
in
  if issquare
    (u/ugcd) then let
    val vgcd = D/ugcd
  in
    if v mod vgcd = 0 then issquare (v/vgcd) else false
  end else false
end // end of [test]

(* ****** ****** *)

// x = 2*u
fun search0 (D: int, x: int): int =
  if test (D, x+1, x-1) then x
  else let
    val v = x/2
  in
    if test (D, v+1, v) then x+1 else search0 (D, x+2)
  end // end of [if]
// end of [search0]

// x = 2*u + 1
fun search1 (D: int, u: int): int =
  if test (D, u, u-1) then 2*u+1 else search1 (D, u+1)
// end of [search1]

(* ****** ****** *)

fun search (D: int): int =
  if issquare (D) then 0
  else if D mod 2 = 0 then search1 (D, 1)
  else search0 (D, 2)
// end of [search]

val x5 = search (5)
val () = assert_errmsg (x5 = 9, #LOCATION)
val x13 = search (13)
val () = assert_errmsg (x13 = 649, #LOCATION)
val x61 = search (61)
val () = assert_errmsg (x61 = 1766319049, #LOCATION)

(* ****** ****** *)

*)

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

fun test (
    D: int, x: &mpz_vt, y: &mpz_vt, tmp1: &mpz_vt, tmp2: &mpz_vt
  ) : bool = let
  val () = mpz_set (tmp1, x)
  val () = mpz_mul (tmp1, x)
  val () = mpz_set (tmp2, y)
  val () = mpz_mul (tmp2, y)
  val () = mpz_mul (tmp2, D)
  val () = mpz_sub (tmp1, tmp2)
in
  (mpz_cmp (tmp1, 1) = 0)
end // end of [test]

(* ****** ****** *)
//
// HX-2010-09-27:
//
// Here is a procedure for solving Pell's equations of the form x^2 - D*y^2 = 1
// where D is square-free
//
// For Pell's equations of the form x^2 - D*y^2 = -1, the approach is the same.
// However, there is no guarantee of a solution in this case.
//
// a(0) = int(sqrt(D))
// P(0) = 0
// P(n+1) = a(n)*Q(n) - P(n)
// Q(0) = 1
// Q(n+1) = (D - (P(n))^2) / Q(n)
// p(0) = a(0)
// p(1) = a(0)*a(1) + 1
// p(n+1) = a(n+1)*p(n+1) + p(n)
// q(0) = 1
// q(1) = a1
// q(n+1) = a(n+1)*q(n+1) + q(n)
//
// Note that p(n)/q(n) consist of the convergents to the continued-fraction
// for sqrt(D)
//
// Finding the first n such that (p(n))^2 - D*(q(n))^2 = 1; the existence of
// such an [n] is guaranteed.
//
fun search
  (D: int, x: &mpz_vt): int = let
//
  val D2 = isqrt (D)
//
  val a0 = D2
  val P0 = 0 and P1 = a0
  val Q0 = 1 and Q1 = D - a0*a0
  val a1 = (a0 + P1) / Q1
//
  fun searchaux (
    n: int
  , x: &mpz_vt
  , p0: &mpz_vt, q0: &mpz_vt // p0 = p(n); q0 = q(n)
  , p1: &mpz_vt, q1: &mpz_vt // p1 = p(n+1); q1 = q(n+1)
  , a: &mpz_vt, P: &mpz_vt, Q: &mpz_vt // a = a(n); P = P(n); Q = Q(n)
  , tmp1: &mpz_vt, tmp2: &mpz_vt
  ) :<cloref1> int = let
    val found = test (D, p0, q0, tmp1, tmp2)
  in
    if found then let
      val () = mpz_set (x, p0)
(*
      val () = (print "aux: found: x = "; print x; print_newline ())
*)
    in
      n // number of trials
    end else let
//
      val () = mpz_mul (tmp1, a, Q)
      val () = mpz_sub (tmp1, P) // tmp1 = a*Q0 - P0
      val () = mpz_set (P, tmp1) // P0 -> P1
//
      val () = mpz_mul (tmp1) // tmp1 = P1*P1
      val () = mpz_set (tmp2, D) // tmp2 = D
      val () = mpz_sub (tmp2, tmp1) // tmp2 = D - P1*P1
      val () = mpz_fdiv_q (tmp2, Q) // tmp2 = (D - P1*P1) / Q0
      val () = mpz_set (Q, tmp2) // Q0 -> Q1
//
      val a1 = (D2 + P1) / Q1
//
      val () = mpz_add (tmp1, P, D2) // tmp1 = P1+D2
      val () = mpz_fdiv_q (a, tmp1, tmp2) // a0 -> a1
//
      val () = mpz_mul (tmp1, a, p1)
      val () = mpz_add (p0, tmp1) // = a2 * p1 + p0
      val () = mpz_mul (tmp2, a, q1)
      val () = mpz_add (q0, tmp2) // = a2 * q1 + q0
//
    in
      searchaux (n+1, x, p1, q1, p0, q0, a, P, Q, tmp1, tmp2)
    end (* end of [if] *)
  end // end of [searchaux]
//
(*
// p0 = a0
// p1 = a0 * a1 + 1
// q0 = 1ULL
// q1 = a1
*)
//
  var p0: mpz_vt; val () = mpz_init_set (p0, a0)
  var q0: mpz_vt; val () = mpz_init_set (q0, 1)
  var p1: mpz_vt; val () = mpz_init_set (p1, a0 * a1 + 1)
  var q1: mpz_vt; val () = mpz_init_set (q1, a1)
  var a: mpz_vt; val () = mpz_init_set (a, a1)
  var P: mpz_vt; val () = mpz_init_set (P, P1)
  var Q: mpz_vt; val () = mpz_init_set (Q, Q1)
  var tmp1: mpz_vt; val () = mpz_init (tmp1)
  var tmp2: mpz_vt; val () = mpz_init (tmp2)
//
  val res = searchaux (0, x, p0, q0, p1, q1, a, P, Q, tmp1, tmp2)
//
  val () = mpz_clear (p0)
  val () = mpz_clear (q0)
  val () = mpz_clear (p1)
  val () = mpz_clear (q1)
  val () = mpz_clear (a)
  val () = mpz_clear (P)
  val () = mpz_clear (Q)
  val () = mpz_clear (tmp1)
  val () = mpz_clear (tmp2)
//
in
  res (* number of trials *)
end // end of [search]

(* ****** ****** *)

implement
main () = () where {
  #define N 1000
  var Dmax: int = 0
//
  var x: mpz_vt
  val () = mpz_init (x)
  var xmax: mpz_vt
  val () = mpz_init_set (xmax, 0)
//
  var D: int // uninitialized
  val () = for
    (D := 1; D <= N; D := D+1)
    if issquarefree (D) then let
//      val () = (print "D = "; print D; print_newline ())
      val _ = search (D, x)
//      val () = (print "x = "; print x; print_newline ())
    in
      if mpz_cmp (x, xmax) > 0 then (Dmax := D; mpz_set (xmax, x))
    end (* end of [if] *)
  // end of [val]
  val () = mpz_clear (x)
  val () = mpz_clear (xmax)
  val ans = Dmax
  val () = assert_errmsg (ans = 661, #LOCATION)
  val () = (print ("ans = "); print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem66-hwxi.dats] *)
