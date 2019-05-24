(*
**
** Some code for testing the following syntax:
**
** for! ... in_list ... do ...
**
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2010
//
(* ****** ****** *)

staload "prelude/SATS/syndef.sats"
staload _(*anon*) = "prelude/DATS/syndef.dats"

(* ****** ****** *)

(*
for! ($x:$T) in_list $exp1 do $exp2 =>
  let
    var x: T?
    var xs: List(T) = $exp1
  in
    while (list_is_cons (xs)) (xs := list_uncons<T> (xs, x); $exp2)
  end
*)

(* ****** ****** *)

#define :: list_cons
typedef intlst = List (int)

(* ****** ****** *)

(*
val xs = (
  1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: list_nil
) : intlst // end of [val]
*)
val xs = $lst_t {int} (tupz! 1 2 3 4 5 6 7 8 9 10)
var i: int = 0
var prod: int = 1
val () = for!
  (x:int) in_list xs do {
  val () = i := i + 1
  val () = if i >= 2 then print "," else ()
  val () = print x
  val () = prod := prod * x
} // end of [val]
val () = print_newline ()
val () = printf ("The product of the list = %i\n", @(prod))

(* ****** ****** *)

implement main () = ()

(* ****** ****** *)

(* end of [forlist.dats] *)
