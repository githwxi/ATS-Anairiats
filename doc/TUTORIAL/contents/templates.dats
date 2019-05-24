//
// code used for illustration in templates.html
//

fun swap_bool_char (xy: @(bool, char)): @(char, bool) = (xy.1, xy.0)

fun swap_int_int (xy: @(int, int)): @(int, int) = (xy.1, xy.0)

fun{a,b:t@ype} swap (xy: @(a, b)): @(b, a) = (xy.1, xy.0)

fun swap_type_type {a,b:type} (xy: @(a, b)): @(b, a) = (xy.1, xy.0)

extern fun{a,b:t@ype} swap (xy: @(a, b)): @(b, a)

implement{a,b} swap (xy) = (xy.1, xy.0)

implement swap<int,int> (xy) = let
  val x = xy.0 and y = xy.1; val s = x + y in (s - x, s - y)
end // end of [swap<int,int>]

(* ****** ****** *)

(* end of [templates.dats] *)
