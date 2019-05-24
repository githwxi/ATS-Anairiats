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

#include "bsearch_arr.dats"

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
  val () = array_ptr_fprint_elt (stdout_ref, !p_arr, N, ", ")
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
//
  extern fun cmp
    (x1: &T, x2: &T): int = "test_cmp"
  implement cmp (x1, x2) = compare (x1, x2)
  extern fun cmp {x1,x2:int}
    (x1: &elt (T, x1), x2: &elt (T, x2)): int (x1-x2) = "test_cmp"
//
  var x0: T = drand48 ()
  prval () = eltencode (x0)
  prval pford = SORT2ORD (pfsrt)
  val (pfmul, pfsrch | p_srch) = bsearch (pford, pflen, pf_arr | p_arr, x0, N, cmp)
  prval () = eltdecode (x0)
//
  prval () = bsearch_ind_isnat (pfsrch)
  prval () = mul_nat_nat_nat (pfmul)
  val pdiff = size1_of_ptrdiff1 (p_srch - p_arr)
  val ind = div_size_size (pdiff, sizeof<T>)
//
  prval pflen_alt = array_of_gfarray {T} (pf_arr)
  prval () = length_isfun (pflen, pflen_alt)
  val () = array_ptr_fprint_elt (stdout_ref, !p_arr, N, ", ")
  val () = print_newline ()
//
  val () = (print "bsearch: x0 = "; print x0; print_newline ())
  val () = (print "bsearch: ind = "; print ind; print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [test_bsearch.dats] *)
