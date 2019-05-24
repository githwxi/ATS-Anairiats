//
// ProjectEuler: Problem 169
// Exploring the number of different ways in which a number can be expressed
// as the sum of 2's powers
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)
//
// f(x) = the number of difference ways in which x can be expressed as the sum
// of 2's powers such that each power can occur at most 2 times.
//
// f(2x+1) = f(x)
// f(2x+2) = f(x+1) + f(x)
// f(2^k(x)) = f(x) + k*f(x-1)
//
(* ****** ****** *)

fun pow5 (n: int): ullint = let
  fun loop (n: int, res: ullint): ullint =
    if n > 0 then loop (n-1, 5ULL * res) else res
  // end of [loop]
in
  loop (n, 1ULL)
end // end of [pow5]

(* ****** ****** *)

fun f (x: ullint): ullint =
  if x >= 2ULL then let
    val r = x mod 2ULL; val x2 = x/2ULL
  in
    if r > 0ULL then f (x2) else f2 (x2, 1U)
  end else 1ULL // end of [if]
// end of [f]

and f2 (x: ullint, k: uint): ullint = let
  val r = x mod 2ULL
in
  if r > 0ULL then f (x) + ullint_of(k) * f (x-1ULL) else f2 (x/2ULL, k+1U)
end // end of [f2]

(* ****** ****** *)

implement main () = let
(*
  val x = pow5 (9)
  val () = (print "x = "; print x; print_newline ())
  val ans = f (x) + 9ULL * f (x-1ULL) // 73411
*)
  val x = pow5 (25)
  val () = (print "x = "; print x; print_newline ())
  val ans = f (x) + 25ULL * f (x-1ULL)
  val () = assert_errmsg (ans = 178653872807ULL, #LOCATION)
in
  (print "ans = "; print ans; print_newline ())
end // end of [main]

(* ****** ****** *)

(* end of [problem169-hwxi.dats] *)
