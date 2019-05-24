//
// ProjectEuler: Problem 80
// Finding decimal representation for irrational square roots
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

fun digitsum
  (x: &mpz_vt, nd: &int? >> int): uint = let
  fun loop (x: &mpz_vt, nd: &int, sum: ulint): ulint =
    if mpz_cmp (x, 0) > 0 then let
      val () = nd := nd+1
      val r = mpz_fdiv_q (x, 10UL) in loop (x, nd, sum+r)
    end else sum
  // end of [loop]
  val () = nd := 0
  val sum = loop (x, nd, 0UL)
in
  uint_of (sum)
end // end of [digitsum]

fun digitsum2
  (nd: int, x: &mpz_vt): uint = let
  fun loop (nd: int, x: &mpz_vt, sum: ulint): ulint =
    if nd > 0 then (
      if mpz_cmp (x, 0) > 0 then let
        val r = mpz_fdiv_q (x, 10UL) in loop (nd-1, x, sum+r)
      end else sum
    ) else sum
  // end of [loop]
  val sum = loop (nd, x, 0UL)
in
  uint_of (sum)
end // end of [digitsum2]

(* ****** ****** *)
//
// HX: the implementation is lengthy but it is memory-clean;
// the run-time footprint of this implementation is tiny!
//
fun qsqrt (
  N: intGte 2, prec: intGte 0, res: &mpq_vt
) : void = let
//
  var _10prec: mpz_vt; val () = mpz_init_set (_10prec, 10UL)
  val () = mpz_pow_ui (_10prec, (ulint_of)prec)
//
  var tmp1: mpz_vt; val () = mpz_init (tmp1)
  var tmp2: mpz_vt; val () = mpz_init_set (tmp2, _10prec)
  val () = mpz_mul (tmp2, _10prec)
  val () = mpz_mul (tmp2, (ulint_of)N)
  var tmp3: mpq_vt; val () = mpq_init (tmp3)
//
  val () = mpq_set (res, ulint_of(N+1), 2UL)
  fun loop (
      tmp1: &mpz_vt, tmp2: &mpz_vt, _10prec: &mpz_vt, tmp3: &mpq_vt
    , res: &mpq_vt
    ) :<cloref1> void = let // n <= res^2
//
    val (pf_nres, fpf_nres | p_nres) =  mpq_numref (res)
    val (pf_dres, fpf_dres | p_dres) =  mpq_denref (res)
//
    val () = mpz_mul (!p_nres, _10prec)
    val () = mpz_fdiv_q (!p_nres, !p_dres)
    val () = mpz_set (!p_dres, _10prec)
//
    val () = mpz_set (tmp1, !p_nres)
    val () = mpz_mul (tmp1, !p_nres)
//
    prval () = fpf_nres (pf_nres)
    prval () = fpf_dres (pf_dres)
  in
    if mpz_cmp (tmp1, tmp2) > 0 then let
      val () = mpq_canonicalize (res)
//
      val () = mpq_inv (tmp3, res)
      val (pf_ntmp3, fpf_ntmp3 | p_ntmp3) =  mpq_numref (tmp3)
      val () = mpz_mul (!p_ntmp3, (ulint_of)N)
      val () = mpq_canonicalize (res)
      prval () = fpf_ntmp3 (pf_ntmp3)
//
      val () = mpq_add (res, tmp3)
      val (pf_dres, fpf_dres | p_dres) =  mpq_denref (res)
      val () = mpz_mul (!p_dres, 2UL)
      prval () = fpf_dres (pf_dres)
      val () = mpq_canonicalize (res)
//
    in
      loop (tmp1, tmp2, _10prec, tmp3, res)
    end (* end of [if] *)
  end // end of [loop]
  val () = loop (tmp1, tmp2, _10prec, tmp3, res)
//
  val () = mpz_clear (_10prec)
  val () = mpz_clear (tmp1); val () = mpz_clear (tmp2)
  val () = mpq_clear (tmp3)
//
(*
  val ans = mpq_get_d (res)
  val () = printf ("sqrt(%i) = %f\n", @(N, ans))
*)
//
in
  // nothing
end // end of [qsqrt]

(* ****** ****** *)

#define NPREC 100

fun qsqrtdigitsum
  (N: intGte 2): uint = let
  var tmp: mpz_vt; val () = mpz_init (tmp)
  var res: mpq_vt; val () = mpq_init (res)
  val () = qsqrt (N, NPREC, res)
//
  val (pf_nres, fpf_nres | p_nres) =  mpq_numref (res)
//
  val () = mpz_set (tmp, !p_nres)
//
  var nd: int
  val sum1 = digitsum (tmp, nd)
  val diff = nd - NPREC
  val sum2 = if diff > 0 then let
    val () = mpz_set (tmp, !p_nres) in digitsum2 (diff, tmp)
  end else 0U // end of [val]
//
  prval () = fpf_nres (pf_nres)
//
  val () = mpz_clear (tmp)
  val () = mpq_clear (res)
in
  sum1 - sum2
end // end of [qsqrtdigitsum]

(* ****** ****** *)

(*
val sum2 = qsqrtdigitsum (2)
val () = (print "sum2 = "; print sum2; print_newline ())
val sum4 = qsqrtdigitsum (4)
val () = (print "sum4 = "; print sum4; print_newline ())
*)

(* ****** ****** *)

fun isSquare (x: int) = let
  val x2 = int_of (sqrt (x+0.5)) in x2 * x2 = x
end // end of [isSquare]

(* ****** ****** *)

implement
main () = () where {
  var sum: uint = 0U
  var N: intGte 2
  val () = for
    (N := 2; N < 100; N := N+1)
    if ~isSquare (N) then sum := sum + qsqrtdigitsum (N)
  // end of [val]
  val ans = sum
  val () = assert_errmsg (ans = 40886U, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem80-hwxi.dats] *)
