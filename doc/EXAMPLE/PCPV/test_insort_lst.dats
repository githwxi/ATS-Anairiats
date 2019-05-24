(*
** Some simple testing code
*)

(* ****** ****** *)

staload "contrib/testing/SATS/randgen.sats"
staload _(*anon*) = "contrib/testing/DATS/randgen.dats"

(* ****** ****** *)

#include "insort_lst.dats"

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

typedef T = double

(* ****** ****** *)

implement randgen<T> () = drand48 ()

(* ****** ****** *)

fun listgen {n:nat}
  (n: int n): list (T, n) = list_randgen<T> (n)
// end of [listgen]

(* ****** ****** *)

fun print_list (xs: List (T), i: int): void =
  case+ xs of
  | list_cons (x, xs) => (
      if i > 0 then print ", "; print x; print_list (xs, i+1)
    ) // end of [list_cons]
  | list_nil () => ()
// end of [print_list]

(* ****** ****** *)

implement
main () = () where {
//
  val () = srand48_with_time ()
//
  #define N 10
  val xs = listgen (N)
  val () = (print_list (xs, 0); print_newline ())
  val (_pf | xs) = gflist_of_list {T} (xs)
  extern fun lte {x1,x2:int} (
    x1: elt (T, x1), x2: elt (T, x2)
  ) : bool (x1 <= x2) = "atspre_lte_double_double"
  val (_pf | ys) = insort<T> (xs, lte)
  val (_pf | ys) = list_of_gflist {T} (ys)
  val () = (print_list (ys, 0); print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [test_insort_lst.dats] *)
