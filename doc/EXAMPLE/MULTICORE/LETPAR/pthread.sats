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
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

// History:
//
// Rui Shi and Hongwei Xi first did [pthread] in ATS/Proto, on which
// this version is primarily based.
//

(* ****** ****** *)

fun pthread_create_detach (f: () -<lin,cloptr1> void): void
  = "ats_pthread_create_detach"

fun pthread_exit (): void // this function does not return
  = "ats_pthread_exit"

(* ****** ****** *)

absviewt@ype pthread_mutex_view_viewt0ype (view)
  = $extype "pthread_mutex_t"

stadef mutex_vt = pthread_mutex_view_viewt0ype

absview pthread_mutex_unlock_ticket_view_addr_viewtype
  (view, addr)

stadef mutex_unlock_ticket =
  pthread_mutex_unlock_ticket_view_addr_viewtype

(* ****** ****** *)

fun pthread_mutex_init {v:view} {l:addr}
  (pf: v | mut: &(mutex_vt v)? >> (mutex_vt v)): void
  = "atslib_pthread_mutex_init"

fun pthread_mutex_create {v:view}
  (pf: v | (*none*)): [l:addr] @(free_gc_v l, mutex_vt v @ l | ptr l)
  = "atslib_pthread_mutex_create"

fun pthread_mutex_destroy {v:view} {l:addr}
  (pf: !mutex_vt v @ l >> (mutex_vt v)? @ l | p: ptr l): @(v | void)
  = "atslib_pthread_mutex_destroy"

fun pthread_mutex_lock {v:view}
  (mutex: &mutex_vt v): [l:addr] @(mutex_unlock_ticket (v, l), v | ptr l)
  = "atslib_pthread_mutex_lock"

fun pthread_mutex_unlock {v:view} {l:addr}
  (ticket: mutex_unlock_ticket (v, l), resource: v | p: ptr l): void
  = "atslib_pthread_mutex_unlock"

(* ****** ****** *)

abstype pthread_mutexref_viewt0ype_type (a: viewt@ype)

stadef mutexref_t = pthread_mutexref_viewt0ype_type

absview pthread_mutexref_unlock_ticket_viewt0ype_addr_view
  (viewt@ype, addr)

stadef mutexref_unlock_ticket = 
  pthread_mutexref_unlock_ticket_viewt0ype_addr_view

fun{a:viewt@ype} pthread_mutexref_create (x: a): mutexref_t a
fun pthread_mutexref_create_tsz {a:viewt@ype} {l:addr}
  (pf: !a @ l >> a? @ l | p: ptr l, tsz: sizeof_t a): mutexref_t a
  = "atslib_pthread_mutexref_create_tsz"

fun pthread_mutexref_lock
  {a:viewt@ype} (mtxrf: mutexref_t a)
  : [l:addr] (mutexref_unlock_ticket (a, l), a @ l | ptr l)
  = "atslib_pthread_mutexref_lock"

fun pthread_mutexref_unlock {a:viewt@ype} {l:addr}
  (_tick: mutexref_unlock_ticket (a, l), _at: a @ l | p: ptr l): void
  = "atslib_pthread_mutexref_unlock"

(* ****** ****** *)

absviewt@ype pthread_cond_viewt0ype
  = $extype "pthread_cond_t"

stadef cond_vt = pthread_cond_viewt0ype

fun pthread_cond_create ()
  : [l:addr] @(free_gc_v l, cond_vt @ l | ptr l)
  = "atslib_pthread_cond_create"

//

fun pthread_cond_wait_mutex {v:view} {l:addr} (
    ticket: !mutex_unlock_ticket (v, l)
  , resource: !v
  | cond: &cond_vt
  , p: ptr l) :<> void
  = "atslib_pthread_cond_wait_mutex"

fun pthread_cond_wait_mutexref {a:viewt@ype} {l:addr} (
    ticket: !mutexref_unlock_ticket (a, l)
  , resource: !a @ l
  | cond: &cond_vt
  , p: ptr l) :<> void
  = "atslib_pthread_cond_wait_mutexref"

symintr pthread_cond_wait
overload pthread_cond_wait with pthread_cond_wait_mutex
overload pthread_cond_wait with pthread_cond_wait_mutexref

//

fun pthread_cond_signal (cond: &cond_vt): void
  = "atslib_pthread_cond_signal"

fun pthread_cond_broadcast (cond: &cond_vt): void
  = "atslib_pthread_cond_broadcast"

(* ****** ****** *)

(* end of [pthread.sats] *)
