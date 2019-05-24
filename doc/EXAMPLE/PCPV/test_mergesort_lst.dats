(*
** Some simple testing code
*)

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "libats/DATS/gflist_vt.dats"

(* ****** ****** *)

staload "contrib/testing/SATS/randgen.sats"
staload _(*anon*) = "contrib/testing/DATS/randgen.dats"
staload "contrib/testing/SATS/fprint.sats"
staload _(*anon*) = "contrib/testing/DATS/fprint.dats"

(* ****** ****** *)

#include "mergesort_lst.dats"

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

typedef T = double

(* ****** ****** *)

implement randgen<T> () = drand48 ()
implement fprint_elt<T> (out, x) = fprint (out, x)

(* ****** ****** *)

fun listgen {n:nat}
  (n: int n): list_vt (T, n) = list_vt_randgen<T> (n)
// end of [listgen]

(* ****** ****** *)

implement
main () = () where {
//
  val () = srand48_with_time ()
//
  #define N 10
(*
  #define N 100,000,000 // HX: this is no problem 
//
// the following timing was recorded on wildwest.bu.edu
// 338.230u 8.491s 5:50.18 99.0% 0+0k 24+232io 0pf+0w
//
*)
//
  val xs = listgen (N)
//
  val () = println! ("The input list has been generated")
  val () = if N <= 100 then
    (list_vt_fprint_elt (stdout_ref, xs, ", "); print_newline ())
  // end of [val]
  prval _pflen = gflist_vt_of_list_vt {T} (xs)
//
  extern fun lte
    (x1: &T, x2: &T): bool = "test_lte"
  implement lte (x1, x2) = x1 <= x2
  extern fun lte {x1,x2:int}
    (x1: &elt (T, x1), x2: &elt (T, x2)): bool (x1 <= x2) = "test_lte"
//
  val (_pfsrt | ys) = mergesort<T> (xs, lte)
//
  prval _pflen = list_vt_of_gflist_vt {T} (ys)
  val ys = ys
  val () = if N <= 100 then
    (list_vt_fprint_elt<T> (stdout_ref, ys, ", "); print_newline ())
  // end of [val]
  val () = list_vt_free (ys)
//
} // end of [main]

(* ****** ****** *)

(* end of [test_mergesort_lst.dats] *)
