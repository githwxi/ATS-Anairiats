//
//
// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//
//

(* ****** ****** *)

%{^

#include "thunk.cats"
#include "pthread.cats"
#include "pthread_locks.cats"

%}

(* ****** ****** *)

staload "pthread.sats"
staload "pthread_locks.sats"
staload "parallel.sats"

(* ****** ****** *)

dynload "parallel.dats"

(* ****** ****** *)

fun fib (n: int): int = if n > 1 then fib (n-1) + fib (n-2) else n

#define CUTOFF 20

fun fib_mt (nfib: Nat): int = begin
(*
  print "fib_mt: nfib = "; print nfib; print_newline ();
*)
  if nfib >= CUTOFF then let
    // this is parallel let-binding
    val par res1 = fib_mt (nfib-1) and res2 = fib_mt (nfib-2)
  in
    res1 + res2
  end else begin
    fib (nfib) // no more parallism
  end // end of [if]
end // end of [fib_mt]

fn fib_usage (cmd: string): void = begin
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
    val () = parallel_worker_add_many (nthread - 1)
    val () = printf ("There are now [%i] workers.", @(nthread))
    val () = print_newline ()
    val res = fib_mt n
  in
    printf ("fib (%i) = %i\n", @(n, res))
  end else begin
    fib_usage argv.[0]; exit (1)
  end
end // end of [main]

(* ****** ****** *)

(* end of [fib_mt.dats] *)
