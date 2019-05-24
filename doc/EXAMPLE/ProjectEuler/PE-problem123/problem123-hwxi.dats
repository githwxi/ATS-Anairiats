//
// ProjectEuler: Problem 123
// Find the remainder of (p_n-1)^n + (p_n+1)^n divided by p_n^2
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
// 1. if n is even, then (x-1)^n+(x+1)^n = 2 (mod x^2)
// 2. if n is odd, then (x-1)^n+(x+1)^x = 2*n*x (mod x^2)
//
// So if n is odd and p_n > 2*n, then
//   (p_n-1)^n+(p_n+1)^n = 2*n*p_n mod (p_n^2)
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

fun isprime (n: int): bool = let
  val r = int_of (sqrt (n + 0.5))
  fun loop (p: int):<cloref1> bool =
    if p <= r then
      (if (n mod p > 0) then loop (p+1) else false)
    else true
  // end of [loop]
in
  if n >= 2 then loop (2) else false
end // end of [isprime]

fun nextprime (n: int): int =
  if isprime n then n else nextprime (n+1)
// end of [nextprime]

(* ****** ****** *)
//
// HX: starting from: search (5, 11)
//
fun search {k:nat}
  (n: int(2*k+1), pn: int, rmax: double): int = let
  val fpn = double_of (pn)
in
  if 2*n*fpn > rmax then n
  else let
    val pn1 = nextprime (pn+1)
    val pn2 = nextprime (pn1+1)
  in
    search {k+1} (n+2, pn2, rmax)
  end // end of [if]
end // end of [search]

(*
// HX: for testing purpose
val ans = search {2} (5, 11, 1E9)
val () = (print "ans = "; print ans; print_newline ())
val () = assert_errmsg (ans = 7037, #LOCATION)
*)
  
(* ****** ****** *)

implement
main () = () where {
  val ans = search {2} (5, 11, 1E10)
  val () = assert_errmsg (ans = 21035, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem123-hwxi.dats] *)
