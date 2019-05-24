//
//
// Author: Hongwei Xi (March 9, 2008)
//
//

%{^

#include "libc/CATS/pthread.cats"
#include "libc/CATS/pthread_locks.cats"

%}

staload "libc/SATS/pthread.sats"
staload _(*anonymous*) = "libc/DATS/pthread.dats"
staload "libc/SATS/pthread_locks.sats"

(* ****** ****** *)

viewtypedef thunk = () -<lin,clo1> void
dataviewtype thunklst (int) =
  | {n:nat} THUNKLSTcons (n+1) of (thunk, thunklst n)
  | THUNKLSTnil (0)

viewtypedef thunklst = [n:nat] thunklst n

typedef sharedworklst = mutexref_t (thunklst)

(* ****** ****** *)

fn sharedworklst_create (): sharedworklst =
  pthread_mutexref_create (THUNKLSTnil ())

val the_sharedworklst = sharedworklst_create ()

(* ****** ****** *)

fn sharedworklst_insert (works: sharedworklst, t: thunk) = let
  val (pf_ticket, pf_at | ptr) = pthread_mutexref_lock (works)
  val () = !ptr := THUNKLSTcons (t, !ptr)
in
  pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
end // end of [sharedworklst_insert]

(* ****** ****** *)

fun sharedworklst_consume (works: sharedworklst): void = let
  val (pf_ticket, pf_at | ptr) = pthread_mutexref_lock (works)
in
  case+ !ptr of
  | ~THUNKLSTcons (t, ts) => let
      val () = (!ptr := ts)
      val () = pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
      val () = pthread_create_detach (t)
    in
      sharedworklst_consume (works)
    end
  | THUNKLSTnil () => let
      val () = fold@ (!ptr)
      val () = pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
    in
      sharedworklst_consume (works)
    end
end // end of [sharedworklst_consume]

(* ****** ****** *)

#define THRESHOLD 36

fun fib (n:int): int = begin
  if n > 1 then let
    val res1 = fib (n-1) and res2 = fib (n-2)
  in
    res1 + res2
  end else begin
    n
  end
end // end of [fib]

// This implementation should be compiled from the above one
// in a straightforward manner (except the value of THRESHOLD):

fun fib_mt (n:int): int = let
  var res1: int and res2: int // uninitialized
in
  if :(res1: int?, res2: int?) => (n >= THRESHOLD) then let

//  the 1st letpar component
    val lock1 = pthread_uplock_create {int @ res1} ()
    val ticket1 = pthread_upticket_create (lock1)
    val thunk1 =
      llam () => let
        val () = (res1 := fib_mt (n-1))
      in
        pthread_upticket_load_and_destroy (view@ res1 | ticket1)
      end
    val () = sharedworklst_insert (the_sharedworklst, thunk1)

//  the 2nd letpar component
    val lock2 = pthread_uplock_create {int @ res2} ()
    val ticket2 = pthread_upticket_create (lock2)
    val thunk2 =
      llam () => let
        val () = (res2 := fib_mt (n-2))
      in
        pthread_upticket_load_and_destroy (view@ res2 | ticket2)
      end
    val () = sharedworklst_insert (the_sharedworklst, thunk2)

//  syncronization point
    val (pf1 | ()) = pthread_uplock_destroy (lock1)
    prval () = view@ res1 := pf1
    val (pf2 | ()) = pthread_uplock_destroy (lock2)
    prval () = view@ res2 := pf2
  in
    res1 + res2 // return value
  end else begin
    fib n // return value
  end // end of [if]
end // end of [fib_mt]

fn fib_usage (cmd: string): void =
  prerrf ("Usage: %s [integer]\n", @(cmd)) // print an error message

implement main (argc, argv) = begin
  if argc >= 2 then let
    val n = int_of argv.[1] // turning string into integer
    val () = begin
      pthread_create_detach (llam () => sharedworklst_consume the_sharedworklst)
    end
    val res = fib_mt n
  in
    printf ("fib (%i) = %i\n", @(n, res))
  end else begin
    fib_usage argv.[0]; exit (1)
  end
end // end of [main]

(* ****** ****** *)

(* end of [fib_mt_unlimited.dats] *)
