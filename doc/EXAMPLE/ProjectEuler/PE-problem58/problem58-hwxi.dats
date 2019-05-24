//
// ProjectEuler: Problem 58
// Investigating the number of primes that lie on the diagnals of a spiral grid
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)

fun isqrt (x: int): int = int_of (sqrt (x+0.5))

fun isprime
  (x: int): bool = let
  val x2 = isqrt (x)
  fun loop (p: int):<cloref1> bool =
    if p <= x2 then
      (if x mod p = 0 then false else loop (p+1))
    else true // end of [if]
in
  if x >= 2 then loop (2) else false
end // end of [isprime]

(* ****** ****** *)

fun LL (k: int) =
  if k = 0 then 1
  else let
    val n = 2*k + 1 in n * n - 2*k
  end // end of [if]

fun UL (k: int) =
  if k = 0 then 1
  else let
    val n = 2*k + 1 in n * n - 4*k
  end // end of [if]

fun UR (k: int) =
  if k = 0 then 1
  else let
    val n = 2*k + 1 in n * n - 6*k
  end // end of [if]

(* ****** ****** *)

fun eval (k: int): int = cnt where {
  var cnt: int = 0
  val () = if isprime (LL(k)) then cnt := cnt + 1
  val () = if isprime (UL(k)) then cnt := cnt + 1
  val () = if isprime (UR(k)) then cnt := cnt + 1
} // end of [eval]

(* ****** ****** *)

implement
main () = () where {
  var k: int = 1
  var cnt: int = 0
  val () = while (true) let
    val () = cnt := cnt + eval (k)
    val ratio = double_of(cnt) / (4*k + 1)
    val () = if ratio < 10.0/100 then break
  in
    k := k + 1
  end // end of [val]
  val ans = 2*k + 1
  val () = assert_errmsg (ans = 26241, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem58-hwxi.dats] *)
