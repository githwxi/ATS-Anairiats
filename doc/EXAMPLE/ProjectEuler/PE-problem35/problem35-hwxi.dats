//
// ProjectEuler: Problem 35
// Finding the number of circular primes under 1M
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

fun isqrt
  (x: uint): uint =
  if x >= 2U then let
    val x4 = x / 4U
    val r2 = isqrt (x4)
    val r = r2 + r2
    val r_1 = r + 1U
  in
    if r_1 * r_1 > x then r else r_1
  end else x 
// end of [isqrt]

(* ****** ****** *)

fn isprime
  {n:nat | n >= 2}
  (n: int n): bool = let
  val u = uint_of_int (n)
  val r = isqrt (u)
(*
  val () = (print "u = "; print u; print_newline ())
  val () = (print "r = "; print r; print_newline ())
*)
  fun loop (p: uint):<cloref1> bool =
    if p <= r then
      (if (u mod p > 0U) then loop (p+1U) else false)
    else true
  // end of [loop]
in
  loop (2U)
end // end of [isprime]

fn isprime
  (n: int): bool = let
  val n = int1_of_int (n)
in
  if n >= 2 then isprime n else false
end // end of [isprime]

(* ****** ****** *)

fun log10 (n: int): int =
  if n > 0 then 1 + log10 (n/10) else 0
// end of [log10]

fun pow10 (N: int): int =
  if N > 0 then 10 * pow10 (N-1) else 1
// end of [pow10]

(* ****** ****** *)

fun test (n: int): bool =
  if isprime (n) then let
    val N = log10 (n)
    val P = pow10 (N-1)
    fun loop
      (n:int, k: int):<cloref1> bool =
      if k <= N then let
        val n1 = P * (n mod 10) + n / 10
      in
        if isprime (n1) then loop (n1, k+1) else false
      end else true
    // end of [loop]
  in
    loop (n, 2)
  end else false // end of [if]
// end of [test]

(* ****** ****** *)

implement main () = () where {
  #define _1M 1000000
  var cnt: int = 0
  var i: int // unintialized
  val () = for (i := 2; i < _1M; i := i + 1) if test (i) then (cnt := cnt + 1)
  val ans = cnt
  val () = assert_errmsg (ans = 55, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem35-hwxi.dats] *)
