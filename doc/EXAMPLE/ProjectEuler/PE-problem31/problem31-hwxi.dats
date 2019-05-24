//
// ProjectEuler: Problem 31
// Finding all the numbers that equal
// the sum of the fifth powers of their digits.
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

val theCoinLst = $lst {int} (1, 2, 5, 10, 20, 50, 100, 200)

(* ****** ****** *)

fun eval (
  cs: List (int), sum: int
) : int =
  if sum = 0 then 1 else (
    case+ cs of
    | list_nil () => 0
    | list_cons (c, cs1) =>
        if sum < 0 then 0 else eval (cs, sum-c) + eval (cs1, sum)
      (* end of [list_cons] *)
  ) // end of [if]
// end of [eval]

(* ****** ****** *)

implement main () = () where {
  val ans = eval (theCoinLst, 200)
  val () = assert_errmsg (ans = 73682, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem31-hwxi.dats] *)
