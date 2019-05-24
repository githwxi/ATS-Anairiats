//
//
// Author: Hongwei Xi (March 10, 2008)
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

staload "libats/SATS/letpar.sats"
staload _(*anonymous*) = "libats/DATS/letpar.dats"

(* ****** ****** *)

dynload "libats/DATS/letpar.dats"

(* ****** ****** *)

absprop GCD (int, int, int)

extern prval gcd_lemma0 {x,y:int} ():<prf> [z:nat] GCD (x, y, z)

extern prval gcd_lemma1 {x,y,z:int} (pf: GCD (x, y, z)):<prf> GCD (x - y, y, z)

extern prval gcd_lemma2 {x,y,z:int} (pf: GCD (x, y, z)):<prf> GCD (x, y - x, z)

extern prval gcd_lemma3 {x:nat;z:int} (pf: GCD (x, x, z)):<prf> [x == z] void

//

viewdef gcd_v (a:addr, b:addr, z:int) =
  [x,y:pos] @(int x @ a, int y @ b, GCD (x, y, z))

//

viewtypedef upticket0 = upticket (void)

fun gcd_flag {a,b:addr} {z:int}
  (pf: !gcd_v (a, b, z) | flag: int, a: ptr a, b: ptr b): bool = let
  prval @(pfa, pfb, pfgcd) = pf
  val x = !a and y = !b
in
  if x > y then begin
    if flag > 0 then let
      val () = (!a := x - y)
      prval () = (pf := @(pfa, pfb, gcd_lemma1 pfgcd))
    in
      gcd_flag (pf | flag, a, b)
    end else begin
      pf := @(pfa, pfb, pfgcd); false // not done
    end
  end else if x < y then begin
    if flag < 0 then let
      val () = (!b := y - x)
      prval () = (pf := @(pfa, pfb, gcd_lemma2 pfgcd))
    in
      gcd_flag (pf | flag, a, b)
    end else begin
      pf := @(pfa, pfb, pfgcd); false // not done
    end
  end else begin
    pf := @(pfa, pfb, pfgcd); true // is done!
  end
end // end of [gcd_flag]

fun gcd_mt {x0,y0:pos} {z:int}
  (pfgcd: GCD (x0, y0, z) | x0: int x0, y0: int y0): int z = let
  var x = x0 and y = y0
  viewtypedef VT = @(gcd_v (x, y, z) | int)
  val ini = @((view@ x, view@ y, pfgcd) | 0)
  val mut: mutexref_t (VT) = pthread_mutexref_create<VT> (ini)
  fun gcd_worker (ticket: upticket0, flag: int):<clo1> void = let
     val (pf_ticket, pf_at | ptr) = pthread_mutexref_lock (mut)
     val done = gcd_flag (ptr->0 | flag, &x, &y)
     val () = pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
   in
     if done then begin
       pthread_upticket_load_and_destroy (() | ticket)
     end else begin
       gcd_worker (ticket, flag)
     end
   end
  val uplock1 = pthread_uplock_create {void} ()
  val upticket1 = pthread_upticket_create {void} (uplock1)
  val () = pthread_create_detach (llam () => gcd_worker (upticket1,  1))

  val uplock2 = pthread_uplock_create {void} ()
  val upticket2 = pthread_upticket_create {void} (uplock2)
  val () = pthread_create_detach (llam () => gcd_worker (upticket2, ~1))

  val (_(*void*) | ()) = pthread_uplock_destroy {void} (uplock1)
  val (_(*void*) | ()) = pthread_uplock_destroy {void} (uplock2)

  val (pf_ticket, pf_at | ptr) = pthread_mutexref_lock (mut)
  prval @(pfa, pfb, pfgcd) = ptr->0
  prval () = (view@ x := pfa; view@ y := pfb)
  val z1 = x and z2 = y
  prval () = begin // this is a serious problem with persistent locks!
    discard (pf_ticket); discard (pf_at)
  end where {
    extern prval discard {v:view} (pf: v):<prf> void
  } // end of [where]
  val () = assert (z1 = z2)
  prval () = gcd_lemma3 (pfgcd)
in
  z1
end // end of [gcd_mt]

fun gcd_main {x,y: pos}
  (x: int x, y: int y): [z:nat] @(GCD (x, y, z) | int z) = let
  prval pf = gcd_lemma0 {x, y} ()
in
  @(pf | gcd_mt (pf | x, y))
end // end of [gcd_main]

//

// This example shows clearly the superiority of multicore over
// singlecore in case of busy waiting.

fn usage (cmd: string): void =
  prerrf ("Usage: %s [positive integer] [positive integer]\n", @(cmd))

implement main (argc, argv) = let
  val () = if argc < 3 then (usage (argv.[0]); exit (1))
  val () = assert (argc >= 3)
  val x = int1_of (argv.[1])
  val () = assert_errmsg (x > 0, "The 1st integer argument is not positive.\n")
  val y = int1_of (argv.[2])
  val () = assert_errmsg (y > 0, "The 2nd integer argument is not positive.\n")
  val @(pf | z) = gcd_main (x, y)
in
  printf (
    "The greatest common divisor of (%i, %i) is %i.\n", @(x, y, z)
  ) // end of [printf]
end // end of [main]

(* ****** ****** *)

(* end of [gcd_mt.dats] *)
