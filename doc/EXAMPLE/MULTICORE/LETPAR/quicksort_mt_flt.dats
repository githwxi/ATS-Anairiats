//
// A parallelized implementation of mergesort
//
// Author: Hongwei Xi (* hwxi AT cs DOT bu DOT edu *)
// Time: March 2008
//

%{^
#include "thunk.cats"
#include "pthread.cats"
#include "pthread_locks.cats"
%}

staload "pthread.sats"
staload "pthread_locks.sats"

(* ****** ****** *)

staload "parallel.sats"
dynload "parallel.dats"

(* ****** ****** *)

#define ARG_QUICKSORT_MT_DATS 1

(*

absviewt@ype T
extern fun lte_T_T (x: !T, y: !T):<> bool
extern fun compare_T_T (x: !T, y: !T):<> Sgn

overload compare with compare_T_T
overload <= with lte_T_T

*)

typedef T = double

(* ****** ****** *)

#include "qsort_mt.dats"

#define CUTOFF 512

fun qsort_mt {n:nat} {A:addr}
  (pf: !array_v (T, n, A) | A: ptr A, n: int n)
  : void = begin
  if n > CUTOFF then let
    val i_pivot = partition (pf | A, n)
    val (pf_mul | ofs) = (size)i_pivot szmul2 sizeof<T>
      prval (pf1, pf2) = array_v_split {T} (pf_mul, pf)
    prval (pf21, pf22) = array_v_uncons {T} (pf2)
    prval pf1_mul = mul_add_const {1} (pf_mul)
    val // par
      () = qsort_mt (pf1 | A, i_pivot)
    and
      () = qsort_mt (pf22 | A+ofs+sizeof<T>, n-i_pivot-1)
    // end of [val]
    prval () = pf2 := array_v_cons {T} (pf21, pf22)
    prval () = pf := array_v_unsplit {T} (pf_mul, pf1, pf2)
  in
    // empty
  end else begin
    qsort (pf | A, n)
  end
end // end of [qsort_mt]

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"

(* ****** ****** *)

fn array_ptr_print {n:nat} {l:addr}
  (pf_arr: !array_v (T, n, l) | A: ptr l, n: size_t n): void = let
  fn f (
    i: sizeLt n, x: &T
  ) :<> void = $effmask_all begin
    if i > 0 then print ", "; printf ("%.2f", @(x))
  end
in
  array_ptr_iforeach_fun<T> (!A, f, n)
end

(* ****** ****** *)

#define N 100.0

extern fun randgen_elt ():<!ref> T
implement randgen_elt () =  N * $Rand.drand48 ()

(* ****** ****** *)

fun
randgen_arr
  {n:nat} .<>.
  (n: int n)
  :<!ref> [l:addr] (
    free_gc_v (T, n, l), array_v (T, n, l)
  | ptr l
  ) = let
  val tsz = sizeof<T>
  val n_sz = size1_of_int1 (n)
  val (pf_gc, pf_arr | p_arr) =
    array_ptr_alloc_tsz {T} (n_sz, tsz)
  // end of [val]
  val () = array_ptr_initialize_fun<T> (!p_arr, n_sz, f) where {
    val f = lam (
      _: sizeLt n
    , x: &(T?) >> T
    ) : void =<fun>
      x := $effmask_all (randgen_elt ())
    // end of [val]
  } // end of [val]
in
  (pf_gc, pf_arr | p_arr)
end // end of [rangen_arr]

(* ****** ****** *)

fn usage (cmd: string): void = begin
  prerr ("Usage:\n");
  prerrf ("  single core: %s [integer]\n", @(cmd));
  prerrf ("  multiple core: %s [integer(arg)] [integer(core)]\n", @(cmd));
end

implement main (argc, argv) = begin
  if argc >= 2 then let
    var nthread: int = 0
    val n = int1_of argv.[1] // turning string into integer
    val () = assert (n >= 0)
    val () = if argc >= 3 then (nthread := int_of argv.[2])
    val () = parallel_worker_add_many (nthread)
    val () = printf ("There are now [%i] workers.", @(nthread))
    val () = print_newline ()
    val (pf_gc, pf_arr | A) = randgen_arr (n)
(*
    val () = array_ptr_print (pf_arr | A, n)
    val () = print_newline ()
*)
    val () = qsort (pf_arr | A, n)
(*
    val () = array_ptr_print (pf_arr | A, n)
    val () = print_newline ()
*)
  in
    array_ptr_free {T} (pf_gc, pf_arr | A)
  end else begin
    usage argv.[0]; exit (1)
  end
end // end of [main]

(* ****** ****** *)

(* end of [quicksort_mt_flt.dats] *)
