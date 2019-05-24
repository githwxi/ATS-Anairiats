//
// ProjectEuler: Problem 44
// Finding a pair of pentagon numbers Pi and Pj such that
// Pi+Pj and D=|Pi-Pj| are also pentagon numbers and D is minized
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload M = "libc/SATS/math.sats"

(* ****** ****** *)

fun isqrt (x: int): int = int_of ($M.sqrt (x + 0.5))

(* ****** ****** *)
//
// x = n(3n-1) / 2
// 3nn - n - 2x = 0
// n = (1 + sqrt (1+24x)) / 6
//
fun isPentagon
  (x: int): bool = let
  val delta = 1 + 24 * x; val q = isqrt (delta)
in
  if q*q = delta then (q + 1) mod 6 = 0 else false
end // end of [isPentagon]

(* ****** ****** *)

fun P(n: int): int = n * (3*n - 1) / 2

(* ****** ****** *)
//
// P(m)-P(n) = 3(mm-nn-(m-n))/2 = (3(m+n)-1)(m-n)/2
//
(* ****** ****** *)

fun test
  (x: int): bool = let
  val y0 = isqrt (x/3)
  fun loop (d: int):<cloref1> bool =
    if d < y0 then let
      val r = x mod d
    in
      if r = 0 then let
        val s3 = x / d + 1
      in
        if s3 mod 3 = 0 then let
          val s = s3 / 3
          val ds = d + s
        in
          if ds mod 2 = 0 then let
            val m = ds / 2; val n = s - m
          in
            if isPentagon (P(m)+P(n)) then let
              val () = printf ("test: m=%i and n=%i\n", @(m,n)) in true
            end else loop (d+1)
          end else loop (d+1)
        end else loop (d+1)
      end else loop (d+1)
    end else false
in
  loop (1)
end // end of [test]

(* ****** ****** *)

fun search
  (n: int): int = let
  val x2 = P(n)
in
  if test (2*x2) then x2 else search (n+1)
end // end of [search]

(* ****** ****** *)

implement
main () = () where {
  val ans = search (1)
  val () = assert_errmsg (ans = 5482660, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem44-hwxi.dats] *)
