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

staload "pthread.sats"

(* ****** ****** *)

absviewtype spawnlock (view)

fun spawnlock_download
  {v:view} (lock: spawnlock v): @(v | void)

(* ****** ****** *)

// [lockview] is for return values indicating whether a lock
// or a view is returned; if a lock is returned, the work load
// may not have been completed yet; if a view is returned, the
// work load was already done by the current thread.

dataviewtype lockview (v:view) =
  | LOCKVIEWlock (v) of spawnlock (v) | LOCKVIEWview (v) of (v | (*none*))

viewtypedef lockview = [v:view] lockview (v)

(* ****** ****** *)

// The maximum number of threads (in addition to the main thread)
// that are allowed to do the work is usually k * N, where k >= 2
// and N is the number of cores available on a machine

fun parallel_worker_add_one (): void // add [1] worker
fun parallel_worker_add_many (n: int): void // add [n] workers

fun parallel_nworker_get (): int // the total number of the workers

(* ****** ****** *)

fun parallel_spawn {v:view}
  (linclo: () -<lin,cloptr1> (v | void)) : lockview (v)
  = "atslib_parallel_spawn"

fun parallel_sync {v:view} (ret: lockview v): @(v | void)
  = "atslib_parallel_sync"

(* ****** ****** *)

(* end of [parallel.sats] *)
