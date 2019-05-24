(*
//
// Some examples for illustrating pattern matching
// Author: Hongwei Xi (September, 2007)
//
*)

(* ****** ****** *)

datatype list0 (a:t@ype) =
  | nil0 (a) | cons0 (a) of (a, list0 a)
// end of [list0]

exception ZipException

fun{a1,a2:t@ype} // [zip0] is a template
zip0 (xs: list0 a1, ys: list0 a2): list0 '(a1, a2) =
  case+ (xs, ys) of // [case+] indicates the exhaustiveness of pattern matching
  | (cons0 (x, xs), cons0 (y, ys)) => cons0 ('(x, y), zip0 (xs, ys))
  | (nil0 (), nil0 ()) => nil0 ()
  | (_, _) => $raise ZipException
// end of [zip0]

(* ****** ****** *)

datatype list1 (a:t@ype, int) =
  | nil1 (a, 0)
  | {n:nat} cons1 (a, n+1) of (a, list1 (a, n))

fun{a1,a2:t@ype} // [zip1] is a template
zip1 {n:nat} (xs: list1 (a1, n), ys: list1 (a2, n)): list1 ('(a1, a2), n) =
  case+ (xs, ys) of // [case+] indicates the exhaustiveness of pattern matching
  | (cons1 (x, xs), cons1 (y, ys)) => cons1 ('(x, y), zip1 (xs, ys))
  | (nil1 (), nil1 ()) => nil1 ()
// end of [zip1]

(* ****** ****** *)

fun{a1,a2:t@ype} // two tag checks
zip1 {n:nat} (xs: list1 (a1, n), ys: list1 (a2, n)): list1 ('(a1, a2), n) =
  case+ (xs, ys) of // [case+] indicates the exhaustiveness of pattern matching
  | (cons1 (x, xs), cons1 (y, ys)) => cons1 ('(x, y), zip1 (xs, ys))
  | (_, _) =>> nil1 ()
// end of [zip1]

fun{a1,a2:t@ype} // only one tag check
zip1 {n:nat} (
  xs: list1 (a1, n), ys: list1 (a2, n)
) : list1 ('(a1, a2), n) = begin
  case+ xs of
  | cons1 (x, xs) => begin
      let val+ cons1 (y, ys) = ys in cons1 ('(x, y), zip1 (xs, ys)) end
    end // end of [cons1]
  | _ =>> nil1 () // end of [nil1]
end // end of [zip1]

(* ****** ****** *)

(* end of [pattern-matching.dats] *)
