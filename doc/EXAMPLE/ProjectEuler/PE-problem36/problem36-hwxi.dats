//
// ProjectEuler: Problem 36
// Finding the sum of all numbers < 1M that are palindromes in both base 2 and base 10
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

fun reverse
  (n: int, base: intGte 2): int = let
  fun loop (n: int, res: int):<cloref1> int =
    if n > 0 then let
      val r = n mod base in loop (n / base, res * base + r)
    end else res
in
  loop (n, 0)
end // end of [reverse]

(* ****** ****** *)

fun test
  (n: int): bool = let
  val r2 = reverse (n, 2)
in
  if (n = r2) then let
    val r10 = reverse (n, 10) in n = r10
  end else false
end // end of [test]

(* ****** ****** *)

implement main () = () where {
  #define N  1000000
  var sum: int = 0
  var i: int // unintialized
  val () = for (i := 1; i < N; i := i+1) if test (i) then sum := sum + i
  val ans = sum
  val () = assert_errmsg (ans = 872187, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem36-hwxi.dats] *)
