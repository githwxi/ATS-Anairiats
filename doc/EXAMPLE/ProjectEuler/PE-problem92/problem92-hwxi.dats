//
// ProjectEuler: Problem 92
// Investigating a square digits number chain with a surprising property
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

fun digitsqrsum
  (x: int): int = let
  fun loop (x: int, sum: int): int =
    if x > 0 then let
      val r = x mod 10 in loop (x / 10, sum + r*r)
    end else sum
  // end of [loop]
in
  loop (x, 0)
end // end of [digitsqrsum]

fun classify (x: int): int =
  if x = 89 then 1 else if x = 1 then 0 else classify (digitsqrsum x)
// end of [classify]

(* ****** ****** *)

implement
main () = () where {
  val N = 10000000 // ten-million
  var i: int = 0
  var c: int = 0
  val () = for
    (i := 1; i < N; i := i+1) c := c + classify (i)
  val ans = c
  val () = assert_errmsg (ans = 8581146, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem92-hwxi.dats] *)
