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
// This version is finished on Sunday, March 9, 2008.

(* ****** ****** *)

staload "libc/SATS/pthread.sats"
staload "libc/SATS/pthread_locks.sats"

(* ****** ****** *)

// [lockview] is for return values indicating whether a lock
// (uplock) or a view is returned; if a lock is returned, a
// thread was spawned to take the work load, which may not have
// been completed yet; if a view is returned, the work load was
// already done by the current thread.

dataviewtype lockview (v:view) =
  | LOCKVIEWlock (v) of uplock (1, v) | LOCKVIEWview (v) of (v | (*none*))

viewtypedef lockview = [v:view] lockview (v)

(* ****** ****** *)

fun letpar_nthreadlock_set (n:int): void

(* ****** ****** *)

fun{a:viewt@ype} letpar {res:addr} {l:addr} (
    pf: a? @ res
  | res: ptr res
  , thunk: () -<lin,clo1> a
  , ret: &lockview? >> lockview (a @ res)
  ) : void

fun letpar_sync {v:view} (ret: lockview v): @(v | void)

(* ****** ****** *)

fun letpar_void {l:addr} (
    thunk: () -<lin,clo1> void
  , ret: &lockview? >> lockview (void)
  ) : void

fun letpar_void_sync (ret: lockview void): void

(* ****** ****** *)

(* end of [letpar.sats] *)
