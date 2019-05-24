//
// ProjectEuler: Problem 34
// Finding the sum of all numbers which are equal to the sum of the factorial of their digits
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

fun fact (n: int): int = if n > 0 then n * fact (n-1) else 1
val fact9 = fact (9)
val () = (print "fact9 = "; print fact9; print_newline ())

fun findBound (n: int, _10_n1: int): int = 
  if n * fact9 >= _10_n1 then findBound (n+1, 10 * _10_n1) else _10_n1
// end of [findBound]

val theBound = findBound (1(*n*), 1(*10^{n-1}*))
val () = (print "theBound = "; print theBound; print_newline ())

(* ****** ****** *)

fun facdigitsum (n: int): int =
  if n > 0 then let
    val r = n mod 10 in facdigitsum (n/10) + fact (r)
  end else 0
// end of [facdigitsum]

(* ****** ****** *)

implement main () = () where {
  #define N theBound
  var sum: int = 0
  var i: int
  val () = for (i := 10; i < N; i := i+1)
    if (i = facdigitsum i) then sum := sum + i
  // end of [val]
  val ans = sum
  val () = assert_errmsg (ans = 40730, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem34-hwxi.dats] *)
