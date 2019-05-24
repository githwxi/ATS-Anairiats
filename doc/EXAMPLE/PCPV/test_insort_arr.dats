(*
** Some simple testing code
*)

(* ****** ****** *)

staload "contrib/testing/SATS/randgen.sats"
staload _(*anon*) = "contrib/testing/DATS/randgen.dats"
staload "contrib/testing/SATS/fprint.sats"
staload _(*anon*) = "contrib/testing/DATS/fprint.dats"

(* ****** ****** *)

#include "insort_arr.dats"

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

typedef T = double

(* ****** ****** *)

implement randgen<T> () = drand48 ()
implement fprint_elt<T> (out, x) = fprint (out, x)

(* ****** ****** *)

implement
main () = () where {
//
  val () = srand48_with_time ()
//
  #define N 10
//
  var !p_arr with pf_arr = @[T][N]()
  val () = array_ptr_randinit<T> (pf_arr | p_arr, N)
//
  val () = array_ptr_fprint_elt<T> (stdout_ref, !p_arr, N, ", ")
  val () = print_newline ()
//
  prval pflen = gfarray_of_array {T} (pf_arr)
//
  extern fun lte
    (x1: &T, x2: &T): bool = "test_lte"
  implement lte (x1, x2) = x1 <= x2
  extern fun lte {x1,x2:int}
    (x1: &elt (T, x1), x2: &elt (T, x2)): bool (x1 <= x2) = "test_lte"
//
  val (pfsrt | ys) = insort<T> (pflen, pf_arr | p_arr, N, lte)
  prval pfperm = SORT2PERM (pfsrt)
  prval pflen = permute_length_lemma (pfperm, pflen)
  prval pflen_alt = array_of_gfarray {T} (pf_arr)
  prval () = length_isfun (pflen, pflen_alt)
//
  val () = array_ptr_fprint_elt<T> (stdout_ref, !p_arr, N, ", ")
  val () = print_newline ()
//
} // end of [main]

(* ****** ****** *)

(* end of [test_insort_arr.dats] *)
