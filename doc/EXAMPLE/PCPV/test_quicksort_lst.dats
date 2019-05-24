(*
** Some simple testing code
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "libats/DATS/gflist.dats"

(* ****** ****** *)

staload "contrib/testing/SATS/randgen.sats"
staload _(*anon*) = "contrib/testing/DATS/randgen.dats"
staload "contrib/testing/SATS/fprint.sats"
staload _(*anon*) = "contrib/testing/DATS/fprint.dats"

(* ****** ****** *)

#include "quicksort_lst.dats"

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

typedef T = double

(* ****** ****** *)

implement randgen<T> () = drand48 ()
implement fprint_elt<T> (out, x) = fprint (out, x)

(* ****** ****** *)

fun listgen {n:nat}
  (n: int n): list (T, n) = list_randgen<T> (n)
// end of [listgen]

(* ****** ****** *)

implement
main () = () where {
//
  val () = srand48_with_time ()
//
  #define N 10
(*
  #define N 1000000
*)
//
  val xs = listgen (N)
  val () = (list_fprint_elt<T> (stdout_ref, xs, ", "); print_newline ())
  val (_pf | xs) = gflist_of_list {T} (xs)
  extern fun lte {x1,x2:int} (
    x1: elt (T, x1), x2: elt (T, x2)
  ) : bool (x1 <= x2) = "atspre_lte_double_double"
  val (_pf | ys) = qsrt<T> (xs, lte)
  val (_pf | ys) = list_of_gflist {T} (ys)
  val () = (list_fprint_elt<T> (stdout_ref, ys, ", "); print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [test_quicksort_lst.dats] *)
