//
// ProjectEuler: Problem 71
// Find the proper fraction n/d < 3/7 such 3/7-n/d is mininal among
// all proper fractions with a denominator <= 1M
//

(* ****** ****** *)
//
// Author Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// (3/7-p/q) = (3q-7p)/7q // find the largest q such that 3q-7p=1 for some p
//
(* ****** ****** *)

implement
main () = () where {
  var q: int = 1000000
  val () = while (true) let
    val () = if (3*q) mod 7 = 1 then break
  in
    q := q - 1
  end // end of [val]
  val ans = (3*q - 1) / 7
  val () = assert (ans = 428570)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem71-hwxi.dats] *)
