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

#define ARG_MERGESORT_MT_DATS 1

(*

absviewt@ype T
extern fun lte_T_T (x: !T, y: !T):<> bool
extern fun compare_T_T (x: !T, y: !T):<> Sgn

overload compare with compare_T_T
overload <= with lte_T_T

*)

typedef T = int

#include "mergesort_mt.dats"

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"

(* ****** ****** *)

fn array_ptr_print {n:nat} {l:addr}
  (pf_arr: !array_v (T, n, l) | A: ptr l, n: size_t n): void = let
  fn f (
    i: sizeLt n, x: &T
  ) :<> void = $effmask_all begin
    if i > 0 then print ", "; printf ("%2d", @(x))
  end
in
  array_ptr_iforeach_fun<T> (!A, f, n)
end

(* ****** ****** *)

#define N 100.0

(* ****** ****** *)

extern fun randgen_elt ():<!ref> T
implement randgen_elt () =  int_of (N * $Rand.drand48 ())

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

#define i2sz size1_of_int1

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
    val () = mergesort (pf_arr | A, (i2sz)n)
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

(* end of [mergesort_mt_int.dats] *)
