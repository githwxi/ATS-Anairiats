//
// ProjectEuler: Problem 100
// Finding the first N > 10^12 such that N(N-1)=2x(x-1) has a integral solution.
//

(* ****** ****** *)
//
// Author Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Septemeber, 2010
//
(* ****** ****** *)
//
// Given N(N-1)=2x(x-1), we have the following equation
// 2N(N-1) + 1 = 4x(x-1) + 1
// So: N^2 + (N-1)^2 = (2x-1)^2
// Clearly, N and N-1 are co-primes.
// So there are p, q, r such that
// p^2+q^2 = 2x-1 and p^2-q^2 = N or N-1
// Note that
// 2(N-1)^2 < (2x-1)^2 < 2N^2
// So sqrt(2)(N-1) < p^2+q^2 < sqrt(2)N
// So (1+sqrt(2))(N-1) < 2p^2 < (1+sqrt(2))N
// So 2(sqrt(2)-1)p2 < N < 2(sqrt(2)-1)p2+1
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)

#define DELTA 0.5

val sqrt2 = sqrt (2.0)

fun test
  (p: int): int (*q*) = let
  val fp = double_of(p)
  val fp2 = fp * fp
  val N = ceil (2 * (sqrt2 - 1) * fp2)
  val (N0, N1) = (
    if fmod (N, 2.0) >= DELTA then @(N-1, N) else @(N, N-1)
  ) : @(double, double)
  val q2 = fp2 - N1
  val q = floor (sqrt(q2 + DELTA))
in
  if q*q = q2 then (if 2*p*q = N0 then int_of(q) else ~1) else ~1
end // end of [test]

(* ****** ****** *)

val () = assert (test (5) >= 0) // N = 21
val () = assert (test (12) >= 0) // N = 120

(* ****** ****** *)

#define _1MM 1E12

implement
main (argc, argv) = () where {
  var x: double = 0.0
  val p0 = sqrt(((sqrt(2.0)+1)*_1MM/2-1))
  val p0 = int_of (p0)
  var p: int
  val () = for
    (p := p0; ; p := p + 1) let
    val q = test (p)
  in
    if q >= 0 then let
      val fp = double_of (p)
      val fq = double_of (q)
      val fp2 = fp * fp
      val fq2 = fq * fq
    in
      if 2*fp*fq >= _1MM then (x := (fp2 + fq2 + 1) / 2; break)
    end (* end of [if] *)
  end // end of [val]
  val ans = (ullint_of)x
  val () = assert_errmsg (ans= 756872327473ULL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem100-hwxi.dats] *)
