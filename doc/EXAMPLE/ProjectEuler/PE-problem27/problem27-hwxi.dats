//
// ProjectEuler: Problem 27
// Finding a quadratic formula of n that produces the maximal number of primes
// for consecutive values of n starting at 0
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

fun isprime {n:nat}
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
  if n >= 2 then loop (2U) else false
end // end of [isprime]

(* ****** ****** *)

fun eval
  (a: int, b: int): int = n where {
  var n: int = 0
  val () = while (true) let
    val x = n * n + a * n + b
    val x = int1_of_int (x)
  in
    if x >= 0 then
      if isprime (x) then (n := n+1) else break
    else break
  end // end of [if]
} // end of [eval]

(* ****** ****** *)

#define N 1000

implement
main () = () where {
  var res: int = 0
  var cnt: int = 0
  var a: int = 0 and b: int = 0
  val () = for
    (b := 1; b < N; b := b+1) let
    val cnt1 = eval (0, b)
    val () = if cnt1 > cnt then cnt := cnt1
  in
    // nothing
  end // end of [val]
  val () = for
    (a := 1; a < N; a := a+1) begin
    for (b := 1; b < N; b := b+1) let
      val cnt1 = eval (a, b)
      val () = if cnt1 > cnt then (cnt := cnt1; res := a * b)
      val cnt1 = eval (~a, b)
      val () = if cnt1 > cnt then (cnt := cnt1; res := ~a * b)
    in
      // nothing
    end // end of [val]
  end // end of [val]
(*
  val () = assert_errmsg (cnt = 71, #LOCATION)
  val () = (print "cnt = "; print cnt; print_newline ())
*)
  val ans = res
  val () = assert_errmsg (ans = ~59231, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem27-hwxi.dats] *)
