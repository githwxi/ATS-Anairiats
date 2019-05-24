//
// ProjectEuler: Problem 94
// Investigating almost-equilateral triangles with integeral area
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX:
// 1. the sides of an equilateral triangle with integral sides cannot be a rational number
// 2.1: case (x, x, x+1): // for x >= 2
// The area of this triangle is sqrt((3x+1)(x+1)(x+1)(x-1))/4
// If the area is integral, then x=2k+1 for some k
// So the area is (k+1)sqrt((3k+2)k); So (3k+2)k is a perfect square
// case (k = 2k1):
//   (3k1+1)k1 is a square; so k1 is a square and (3k1+1) is also a sqare
// case (k = 2k1+1): so k is a sqare and 3k+2 is also a square but this is
// impossible (considering the (mod-3) operation)
//
// 2.2: case (x, x, x-1): // for x >= 2
// The area of this triangle is sqrt((3x-1)(x-1)(x-1)(x+1))/4
// If the area is integral, then x=2k+1 for some k
// So the area is (k)sqrt((3k+1)(k+1)); So (3k+1)(k+1) is a perfect square
// case (k=2k1): Then 3k+1 and k+1 are squares
// case (k=2k1+1): so (3k1+2) and (k1+1) are squares but this is impossible
// (considering the (mod-3) operation)
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)

fun isqrt (x: int): int = int_of (sqrt(x+0.5))
fun isSquare (x: int): bool = let val r = isqrt (x) in r*r = x end

(* ****** ****** *)
//
// testing if (3k+2)*k is a perfect square
//
fun test1 {k:nat} (k: int k): bool =
  if k mod 2 = 0 then let
    val k1 = k / 2 in if isSquare(k1) then isSquare(3*k1+1) else false
  end else false // end of [if]
// end of [test1]

(* ****** ****** *)
//
// testing if (3k+1)*(k+1) is a perfect square
//
fun test2 {k:nat} (k: int k): bool =
  if k mod 2 = 0 then begin
    if isSquare(k+1) then isSquare(3*k+1) else false
  end else false // end of [if]
// end of [test2]

(* ****** ****** *)

fun pow (x: int, n: int): int =
  if n > 0 then x * pow (x, n-1) else 1
// end of [pow]

(* ****** ****** *)

implement
main () = () where {
  val Nx = (pow (10, 9) - 1) / 3
  val Nk = (Nx - 1) / 2
  var sum: int = 0
  var k: Nat // uninitialized
  val () = for
    (k := 2; k <= Nk; k := k+1) let
    val () = if test1 (k) then let
      // val () = (print "test1: k = "; print k; print_newline ())
      in sum := sum + (6*k+4)
    end // end of [val]
    val () = if test2 (k) then let
      // val () = (print "test2: k = "; print k; print_newline ())
      in sum := sum + (6*k+2)
    end // end of [val]
  in
    // nothing
  end // end of [val]
  val ans = sum
  val () = assert_errmsg (ans = 518408346, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem94-hwxi.dats] *)
