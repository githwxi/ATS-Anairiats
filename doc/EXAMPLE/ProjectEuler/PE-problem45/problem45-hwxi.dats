//
// ProjectEuler: Problem 45
// Finding the first triangle number after 40755
// that is also a pentagon and a hexagon.
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload M = "libc/SATS/math.sats"

(* ****** ****** *)

fun isqrt (x: ullint): int = int_of ($M.sqrt ((double_of)x + 0.5))

(* ****** ****** *)
//
// x = n(3n-1) / 2
// 3nn - n - 2x = 0
// n = (1 + sqrt (1+24x)) / 6
//
fun isPentagon
  (x: ullint): bool = let
  val delta = 24ULL * x + 1ULL
  val q = isqrt (delta); val q1 = ullint_of(q)
in
  if q1*q1 = delta then (q + 1) mod 6 = 0 else false
end // end of [isPentagon]

(* ****** ****** *)

fun H(n: int): ullint = let
  val n = ullint_of(n) in n*(2ULL*n-1ULL)
end // end of [H]

(* ****** ****** *)
//
// m(m+1)/2 = n(2n-1) =>
// m(m+1) = (2n-1)2n => m = 2n-1
// So, a hexagon number is always a triangle one
//
(* ****** ****** *)

fun search
  (n: int, cnt: int): ullint = let
  val x = H(n)
in
  if isPentagon (x) then
    if cnt = 0 then search (n+1, 1) else x
  else search (n+1, cnt)
end // end of [search]

(* ****** ****** *)

implement
main () = () where {
  val ans = search (2, 0)
  val () = assert_errmsg (ans = 1533776805ULL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem45-hwxi.dats] *)
