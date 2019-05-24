(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// Some functions for supporting multicore programming
// This version is finished on Sunday, March 9, 2008

(* ****** ****** *)

%{^

#ifndef ATS_MULTITHREAD
#define ATS_MULTITHREAD
#endif

#include "libc/CATS/pthread.cats"
#include "libc/CATS/pthread_locks.cats"

%}

staload "libc/SATS/pthread.sats"
staload "libc/SATS/pthread_locks.sats"

(* ****** ****** *)

staload "letpar_old.sats"

(* ****** ****** *)

#define NTHREADMAX 16

extern val the_letpar_nthreadlock: mutexref_t (int)

implement the_letpar_nthreadlock = let
  var n = NTHREADMAX
in
  pthread_mutexref_create_tsz {int} (view@ n | &n, sizeof<int>)
end

(* ****** ****** *)

fun letpar_nthreadlock_get (): int = let
  val (pf_ticket, pf_at | ptr) =
    pthread_mutexref_lock (the_letpar_nthreadlock)
  val n = !ptr
in
  pthread_mutexref_unlock (pf_ticket, pf_at | ptr); n
end // end of [letpar_nthreadlock_set]

implement letpar_nthreadlock_set (n) = let
  val (pf_ticket, pf_at | ptr) =
    pthread_mutexref_lock (the_letpar_nthreadlock)
  val () = !ptr := n
in
  pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
end // end of [letpar_nthreadlock_set]

(* ****** ****** *)

extern fun letpar_nthreadlock_increase (): void

implement letpar_nthreadlock_increase () = let
  val (pf_ticket, pf_at | ptr) =
    pthread_mutexref_lock (the_letpar_nthreadlock)
  val () = !ptr := !ptr + 1
in
  pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
end // end of [letpar_nthreadlock_increase]

(* ****** ****** *)

implement letpar<a> {res} (pf | res, thunk, ret) = let
  val (pf_ticket, pf_at | ptr) =
    pthread_mutexref_lock (the_letpar_nthreadlock)
  val n = !ptr
in
  if :(ret: lockview (a @ res)) => n > 0 then let
    val () = (!ptr := n-1)
    val () = pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
    val lock = pthread_uplock_create {a @ res} ()
    val ticket = pthread_upticket_create (lock)
    val () = (ret := LOCKVIEWlock lock)
    val thunk =
      llam () => let
        val () = (!res := thunk ())
        val () = begin
          pthread_upticket_load_and_destroy (view@ (!res) | ticket)
        end
      in
        letpar_nthreadlock_increase ()
      end
  in
    pthread_create_detach (thunk)
  end else let
    val () = pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
    val () = !res := thunk ()
  in
    ret := LOCKVIEWview (view@ (!res) | (*none*))
  end
end // end of [letpar]

implement letpar_sync (ret) = begin case+ ret of
  | ~LOCKVIEWlock lock => pthread_uplock_destroy (lock)
  | ~LOCKVIEWview (pf | (*none*)) => (pf | ())
end // end of [letpar_syn]

(* ****** ****** *)

extern prval void ():<prf> void

implement letpar_void (thunk, ret) = let
  val (pf_ticket, pf_at | ptr) =
    pthread_mutexref_lock (the_letpar_nthreadlock)
  val n = !ptr
in
  if :(ret: lockview (void)) => n > 0 then let
    val () = (!ptr := n-1)
    val () = pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
    val lock = pthread_uplock_create {void} ()
    val ticket = pthread_upticket_create (lock)
    val () = (ret := LOCKVIEWlock lock)
    val thunk =
      llam () => let
        val () = thunk ()
        val () = begin
          pthread_upticket_load_and_destroy (void () | ticket)
        end
      in
        letpar_nthreadlock_increase ()
      end
  in
    pthread_create_detach (thunk)
  end else let
    val () = pthread_mutexref_unlock (pf_ticket, pf_at | ptr)
    val () = thunk ()
  in
    ret := LOCKVIEWview (void () | (*none*))
  end
end // end of [letpar_void]

implement letpar_void_sync (ret) = begin case+ ret of
  | ~LOCKVIEWlock lock => begin
      let val (pf | ()) = pthread_uplock_destroy (lock) in () end
    end
  | ~LOCKVIEWview (pf | (*none*)) => ()
end // end of [letpar_void_syn]

(* ****** ****** *)

(* end of [letpar.dats] *)
