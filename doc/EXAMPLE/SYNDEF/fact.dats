(*
** some code for testing the do-while syntax
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2010
//
(* ****** ****** *)

fun fact
  {n:pos} .<>.
  (n: int n): int = let
  var n: int = n
  var res: int = 1
  val () = do! {
    val () = res := n * res; val () = n := n-1
  } while (n >= 1) // end of [val]
in
  res
end // end of [fact]

implement main () = let
  val ans = fact (10) in println! ("10! = ", ans)
end // end of [main]

(* ****** ****** *)

(* end of [fact.dats] *)