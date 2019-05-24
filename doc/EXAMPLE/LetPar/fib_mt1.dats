//
//
// Author: Hongwei Xi (March 9, 2008)
//
//

%{^
#include "libats/CATS/thunk.cats"
%}

staload "libc/SATS/pthread.sats"
staload "libc/SATS/pthread_uplock.sats"

(* ****** ****** *)

(*
staload "libats/SATS/letpar.sats"
staload _(*anonymous*) = "libats/DATS/letpar.dats"
*)

(* ****** ****** *)

(*
dynload "libats/DATS/letpar.dats"
*)

(* ****** ****** *)

#define NFIB 30

// This implementation should be compiled from the above one
// in a straightforward manner (except the value of NFIB):

fun fib_mt (nfib:int): int = let
  var res1: int and res2: int // uninitialized
  var ret1: lockview? and ret2: lockview?
in
  if :(res1: int?, res2: int?) => (nfib >= NFIB) then let

//  the letpar components
    val () = letpar<int> (
      view@ res1 | &res1, llam () => fib_mt (nfib-1), ret1
    ) // end of [letpar]

    val () = letpar<int> (
      view@ res2 | &res2, llam () => fib_mt (nfib-2), ret2
    ) // end of [letpar]

//  syncronization point
    val (pf1 | ()) = letpar_sync ret1; prval () = view@ res1 := pf1
    val (pf2 | ()) = letpar_sync ret2; prval () = view@ res2 := pf2
  in
    res1 + res2 // return value
  end else begin
    (if nfib > 1 then fib_mt (nfib-1)+ fib_mt (nfib-2) else nfib)
  end // end of [if]
end // end of [fib_mt]
////
fn fib_usage (cmd: string): void = begin
  prerr ("Usage:\n");
  prerrf ("  single core: %s [integer]\n", @(cmd));
  prerrf ("  multiple core: %s [integer(arg)] [integer(core)]\n", @(cmd));
end

implement main (argc, argv) = begin
  if argc >= 2 then let
    var nthread: int = 0
    val n = int_of argv.[1] // turning string into integer
    val () = if argc >= 3 then (nthread := int_of argv.[2])
    val () = letpar_worker_add_many (nthread)
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
