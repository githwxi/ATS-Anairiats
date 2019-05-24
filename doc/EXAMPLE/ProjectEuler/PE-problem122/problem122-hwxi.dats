//
// ProjectEuler: Problem 122
// Finding the minimal number of multiplication operations needed to
// compute x^n
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload "prelude/DATS/list.dats"

(* ****** ****** *)

typedef intlst = List int
#define :: list_cons
#define cons list_cons
#define nil list_nil
macdef sing (x) = cons (,(x), nil)

(* ****** ****** *)

fun print_intlst (xs: intlst): void =
  case+ xs of
  | cons (x, xs) => (print x; print ","; print_intlst xs)
  | nil () => ()
// end of [print_intlst]
overload print with print_intlst

(* ****** ****** *)

fun dmineval (k: int): int =
  if k > 1 then let
    val r = k mod 2 in
    if r = 0 then 1 + dmineval (k/2) else 2 + dmineval (k/2)
  end else 0 // end of [if]
// end of [dmineval]

(* ****** ****** *)
//
// HX: the search is not really efficient, but it is efficient enough to
// get the job done in about 1 second
//
fun search (k: int): int = let
  val d0 = dmineval (k)
  fun aux0 (
      k: int, dmin: int, x0: int, xs0: intlst, d: int // d+1 < dmin
    ) : int =
    aux1 (k, dmin, x0, xs0, xs0, d)
  and aux1 (
    k: int, dmin: int, x0: int, xs0: intlst, xs1: intlst, d: int
  ) : int =
    case+ xs1 of
    | cons (x1, xs11) => aux2 (k, dmin, x0, xs0, x1, xs11, xs1, d: int)
    | nil () => dmin
  and aux2 (
    k: int
  , dmin: int, x0: int, xs0: intlst, x1: int, xs11: intlst, xs2: intlst, d: int
  ) : int =
    case+ xs2 of
    | cons (x2, xs21) => let
        val x12 = x1 + x2
      in
        if x12 <= x0 then dmin
        else if x12 < k then let
          val dmin = (
            if d+2 < dmin then let
              val x0 = x12 and xs0 = cons (x12, xs0) in aux0 (k, dmin, x0, xs0, d+1)
            end else dmin
          ) : int // end of [val]
        in
          if d+1 < dmin then aux2 (k, dmin, x0, xs0, x1, xs11, xs21, d) else dmin
        end else (
          if x12 > k then aux2 (k, dmin, x0, xs0, x1, xs11, xs21, d) else d+1
        ) // end of [if]
      end // end of [cons]
    | nil () => aux1 (k, dmin, x0, xs0, xs11, d)
in
  if d0 >= 2 then aux0 (k, d0, 1, sing (1), 0) else d0
end // end of [search]

val () = assert_errmsg (search (15) = 5, #LOCATION)

(* ****** ****** *)

implement main () = () where {
  val N = 200
  fun loop (k: int, sum: int): int =
    if k <= N then let
//      val () = (print "loop: k = "; print k; print_newline ())
      val mk = search (k)
//      val () = (print "loop: m(k) = "; print mk; print_newline ())
    in
      loop (k+1, sum + mk)
    end else sum // end of [loop]
  val ans = loop (1, 0)
  val () = assert_errmsg (ans = 1582, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem122-hwxi.dats] *)
