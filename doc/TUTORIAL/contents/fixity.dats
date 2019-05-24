(*

//
// Author: Hongwei Xi (January, 2009)
//

*)

postfix (imul + 10) !!
extern fun !! (x: int): int
implement !! (x) = if x >= 2 then x * (x - 2)!! else 1

(* ****** ****** *)

implement main () = begin
  printf ("10!! = %i\n", @(10!!))
end // end of [main]

(* ****** ****** *)

(* end of [fixity.dats] *)
