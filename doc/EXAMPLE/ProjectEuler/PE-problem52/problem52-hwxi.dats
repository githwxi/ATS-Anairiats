//
// ProjectEuler: Problem 52
// Finding the smallest positive natural number x such that
// x, 2x, 3x, 4x, 5x, and 6x have the same digits
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

fun insert {n:nat} .<n>.
  (x0: int, xs: list_vt (int, n)): list_vt (int, n+1) =
  case+ xs of
  | list_vt_cons (x, !p_xs1) =>
      if x0 <= x then
        (fold@ xs; list_vt_cons (x0, xs))
      else
        (!p_xs1 := insert (x0, !p_xs1); fold@ xs; xs)
      // end of [if]
  | list_vt_nil () => (fold@ xs; list_vt_cons (x0, xs))
// end of [insert]

(* ****** ****** *)

fun toDigits (x: int): List_vt (int) =
  if x > 0 then let
    val r = x mod 10 in insert (r, toDigits (x/10))
  end else list_vt_nil
// end of [toDigits]

(* ****** ****** *)

fun eq_intlst_intlst {n1,n2:nat} .<n1>.
  (xs: !list_vt (int, n1), ys: !list_vt (int, n2)): bool =
  case+ xs of
  | list_vt_cons (x, !p_xs) => (case+ ys of
    | list_vt_cons (y, !p_ys) => let
        val res = (if x = y then eq_intlst_intlst (!p_xs, !p_ys) else false): bool
      in
        fold@ xs; fold@ ys; res
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ xs; fold@ ys; false)
    ) // end of [list_vt_cons]
  | list_vt_nil () => (case+ ys of
    | list_vt_cons _ => (fold@ xs; fold@ ys; false)
    | list_vt_nil () => (fold@ xs; fold@ ys; true)
    )  // end of [list_vt_nil]
// end of [eq_intlst_intlst]

(* ****** ****** *)

fun test1 {n:nat}
  (N: int, x: int, ds: !list_vt (int, n), n: int): bool =
  if n <= N then let
    val x1 = n * x
    val ds1 = toDigits (x1)
    val res = eq_intlst_intlst (ds, ds1)
    val () = list_vt_free (ds1)
  in
    if res then test1 (N, x, ds, n+1) else false
  end else true

fun test
  (N: int, x: int): bool = let
  val ds = toDigits (x)
  val res = test1 (N, x, ds, 2)
  val () = list_vt_free (ds)
in
  res
end // end of [test]

val () = assert_errmsg (test (2, 125874), #LOCATION)

(* ****** ****** *)

fun pow10 (n: int): int = if n > 0 then 10 * pow10 (n-1) else 1

(* ****** ****** *)

fun search (k: int): int = let
(*
  val () = (print "search: k = "; print k; print_newline ())
*)
  fun loop
    (x: int, X: int):<cloref1> int =
    if x <= X then
      if test (6, x) then x else loop (x+1, X)
    else search (k+1)
  val x0 = pow10 (k-1)
  val X0 = (10 * x0 - 1) / 6
in
  loop (x0, X0)
end // end of [search]

(* ****** ****** *)

implement main () = () where {
  val ans = search (1)
  val () = assert_errmsg (ans = 142857, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem52-hwxi.dats] *)
