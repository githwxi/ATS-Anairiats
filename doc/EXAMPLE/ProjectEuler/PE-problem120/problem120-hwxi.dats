//
// ProjectEuler: Problem 120
// Find the maximum remainder of (a-1)^n+(a+1)^n divided by a^2
//

(* ****** ****** *)
//
// Author Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX:
//
// 1. if n is even, then (a-1)^n+(a+1)^n = 2 (mod a^2)
// 2. if n is odd, then (a-1)^n+(a+1)^n = 2*n*a (mod a^2)
//
// So rmax (a) = (a-1)*a if a is odd (for a >= 3)
// So rmax (a) = (a-2)*a if a is even (for a >= 2)
//
// So, Sigma_{3<=a<=1000} rmax (a) =
// Sigma_{1<=k<=499} 2*k(2*k+1) + Sigma_{1<=k<=499} 2*k(2*k+2) =
// Sigma_{1<=k<=499} 2*k(4*k+3) =
// Sigma_{1<=k<=499} (8*k^2+6*k)
//
(* ****** ****** *)

implement
main () = () where {
  val k = 499
  val k2 = k*(k+1)
  val ans = 8*k2*(2*k+1)/6 + 6*k2/2
  val () = assert_errmsg (ans = 333082500, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem120-hwxi.dats] *)
