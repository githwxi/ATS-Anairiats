(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)


(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: March 2008
//
(* ****** ****** *)

// Some functions for supporting multicore programming

//
// This is the *first* concrete example I did in which
// a (simple) locking order is statically enforced to
// prevent potential deadlocks. Though the underlying
// strategy is quite involved and certainly needs some
// improvement, the result it ensures is gratifying!
//

(* ****** ****** *)

%{^

#ifndef ATS_MULTITHREAD
#define ATS_MULTITHREAD
#endif

#include "thunk.cats"
#include "pthread.cats"
#include "pthread_locks.cats"

%}

staload "thunk.sats"
staload "pthread.sats"
staload "pthread_locks.sats"

(* ****** ****** *)

staload "parallel.sats"

(* ****** ****** *)

viewtypedef TQ = @{ T= Thunkopt, Q= int (* queue status *)}

abstype lock1_t // = mutexref_t TQ
absview lock1_unlock_ticket (addr)
absview lockord1


abstype lock2_t // = mutexref_t (MClst)
absview lock2_unlock_ticket (addr)
absview lockord2

viewdef lockord12 = @(lockord1, lockord2)
extern prval parallel_spawn_lockordbox: vbox lockord12

(* ****** ****** *)

typedef C = ref (cond_vt)
typedef M = lock1_t
typedef MC = '{ m=M, c=C, id= int }
viewtypedef MClst = List_vt MC

typedef NTHREAD = lock2_t

(* ****** ****** *)

assume spawnlock (v:view) = uplock (1, v)

implement spawnlock_download (lock) = pthread_uplock_download (lock)

(* ****** ****** *)

%{^

static __thread ats_ptr_type the_mc_per_thread ;

static inline
ats_ptr_type ats_parallel_mc_per_thread_get () {
  return the_mc_per_thread ;
}

static inline
ats_void_type ats_parallel_mc_per_thread_set (ats_ptr_type mc) {
  the_mc_per_thread = mc ; return ;
}

%}

extern fun mc_per_thread_get ():<> MC
  = "ats_parallel_mc_per_thread_get"

extern fun mc_per_thread_set (mc: MC):<> void
  = "ats_parallel_mc_per_thread_set"

(* ****** ****** *)

(*

//
// Here is the locking order:
//
// If [lock2] is locked, then [lock1] can no longer be locked
// until [lock2] is unlocked
//

*)

extern
fun pthread_create_detached_lockord12
  (thunk: (!lockord12 | (*none*)) -<lin,cloptr1> void): void
  = "ats_pthread_create_detached"

extern
fun lock1_create_tsz {l:addr}
  (pf: !TQ @ l >> TQ? @ l | p: ptr l , tsz: sizeof_t TQ) : lock1_t
  = "atslib_pthread_mutexref_create_tsz"

extern
fun lock1_lock
  (_ord1: lockord1, _ord2: !lockord2 | m: lock1_t)
  :<> [l:addr] (lock1_unlock_ticket l, TQ @ l | ptr l)
  = "atslib_pthread_mutexref_lock"

extern
fun lock1_unlock {l:addr}
  (_ticket: lock1_unlock_ticket l, _at: TQ @ l | p: ptr l)
  :<> (lockord1 | void)
  = "atslib_pthread_mutexref_unlock"

extern
fun cond_wait_lock1 {l:addr} (
  _ord2: !lockord2
, _ticket: !lock1_unlock_ticket l
, _at: !TQ @ l
| cond: &cond_vt
, p: ptr l
) :<> void
  = "atslib_pthread_cond_wait_mutexref"

//

extern
fun lock2_create_tsz {l:addr} (
  pf: !MClst @ l >> MClst? @ l
| p: ptr l
, tsz: sizeof_t (MClst)
):<> lock2_t
  = "atslib_pthread_mutexref_create_tsz"

extern
fun lock2_lock (
  _ord2: lockord2 | m: lock2_t
) :<> [l:addr] (lock2_unlock_ticket l, MClst @ l | ptr l)
  = "atslib_pthread_mutexref_lock"

extern
fun lock2_unlock {l:addr} (
  _ticket: lock2_unlock_ticket l, _at: MClst @ l | p: ptr l
) :<> (lockord2 | void)
  = "atslib_pthread_mutexref_unlock"

(* ****** ****** *)

extern val parallel_nthread: NTHREAD

implement parallel_nthread = let
  var mcs: MClst = list_vt_nil ()
in
  lock2_create_tsz (view@ mcs | &mcs, sizeof<MClst>)
end

(* ****** ****** *)

fn mc_enque2 (pford2: !lockord2 | mc: MC):<> void = let
(*
  val () = $effmask_all begin
    print "mc_enque2: begin: mc.id = "; print mc.id; print_newline ()
  end
*)
  val (pf2_ticket, pf2_at  | ptr2) = lock2_lock (pford2 | parallel_nthread)
  val () = (!ptr2 := list_vt_cons (mc, !ptr2))
  val (pford2_new | ()) = lock2_unlock (pf2_ticket, pf2_at | ptr2)
(*
  val () = $effmask_all begin
    print "mc_enque2: finish: mc.id = "; print mc.id; print_newline ()
  end
*)
in
  pford2 := pford2_new
end // end of [mc_enque2]

fn mc_enque12
  (pford1: !lockord1, pford2: !lockord2 | mc: MC):<> void = let
(*
  val () = $effmask_all begin
    print "mc_enque12: begin: mc.id = "; print mc.id; print_newline ()
  end
*)
  val (pf1_ticket, pf1_at | ptr1) = lock1_lock (pford1, pford2 | mc.m)
  val () =
    if thunkopt_is_none (ptr1->T) then let
      val xQ = ptr1->Q
      val () = if xQ <> 1 then ptr1->Q := 1 // it is enqueued
    in
      if xQ = 0 then mc_enque2 (pford2 | mc)
    end
  val (pford1_new | ()) = lock1_unlock (pf1_ticket, pf1_at | ptr1)
(*
  val () = $effmask_all begin
    print "mc_enque12: finish: mc.id = "; print mc.id; print_newline ()
  end
*)
in
  pford1 := pford1_new
end // end of [mc_enque12]

(* ****** ****** *)

fun worker_fun
  (pford12: !(lockord1, lockord2) | mc: MC): void = let
(*
  val mc_self = mc_per_thread_get ()
  val () = begin
    print "worker_fun: mc_self.id = "; print mc_self.id; print_newline ()
  end
*)
  prval @(pford1, pford2) = pford12
  val (pf1_ticket, pf1_at | ptr1) = lock1_lock (pford1, pford2 | mc.m)
  val (pford1 | ()) = worker_fun_cont (pf1_ticket, pf1_at, pford2 | ptr1, mc)
in
  pford12 := @(pford1, pford2)
end

and worker_fun_cont {l:addr} (
    pf1_ticket: lock1_unlock_ticket l
  , pf1_at: TQ @ l
  , pford2: !lockord2
  | ptr1: ptr l
  , mc: MC
  ) : @(lockord1 | void) = let
(*
  val () = begin
    print "worker_fun_cont: "; print_newline ()
  end
*)
  val xT = ptr1->T; val () = ptr1->T := thunkopt_none()
in
  if thunkopt_is_some (xT) then let
(*
    val () = begin
      print "worker_fun_cont: thunkopt_some: 1"; print_newline ()
    end
*)
    val (pford1 | ()) = lock1_unlock (pf1_ticket, pf1_at | ptr1)
(*
    val () = begin
      print "worker_fun_cont: thunkopt_some: 2"; print_newline ()
    end
*)
    val () = thunk_exec (thunkopt_unsome xT)
(*
    val () = begin
      print "worker_fun_cont: thunkopt_some: 3"; print_newline ()
    end
*)
    val () = mc_enque12 (pford1, pford2 | mc)
    prval pford12 = @(pford1, pford2)
    val () = worker_fun (pford12 | mc)
    prval @(pford1, pford2_new) = pford12
  in
    pford2 := pford2_new; (pford1 | ())
  end else let
(*
    val () = begin
      print "worker_fun_cont: thunkopt_none"; print_newline ()
    end
*)
    val () = thunkopt_unnone (xT)
    val () = let
      val (vbox pf_cond | p_cond) = ref_get_view_ptr (mc.c)
    in
      cond_wait_lock1 (pford2, pf1_ticket, pf1_at | !p_cond, ptr1)
    end
  in
    worker_fun_cont (pf1_ticket, pf1_at, pford2 | ptr1, mc)
  end
end // end of [worker_fun_cont]

(* ****** ****** *)

local
  var ini: int = 0
  val nworker_ref: ref int = ref_make_elt_tsz (ini, sizeof<int>)
  var ini: int = 0
  val workerid_ref: ref int = ref_make_elt_tsz (ini, sizeof<int>)
in
  fn nworker_get (): int = !nworker_ref

  fn nworker_inc (): void = begin
    let val nworker = !nworker_ref in !nworker_ref := nworker + 1 end
  end

  fn nworker_dec (): void = begin
    let val nworker = !nworker_ref in !nworker_ref := nworker - 1 end
  end

  fn workerid_gen () = let
    val id = !workerid_ref; val () = !workerid_ref := id + 1
  in
    id
  end // end of [workerid_gen]
end // end of [local]

(* ****** ****** *)

implement parallel_nworker_get () = nworker_get ()

fn parallel_mc_make (): MC = let
  var x: TQ; val () = x.T := thunkopt_none(); val () = x.Q := 0
  val m = lock1_create_tsz (view@ x | &x, sizeof<TQ>)
  val (pf_gc, pf_at | ptr) = pthread_cond_create ()
  prval () = free_gc_elim (pf_gc)
  val c = ref_make_view_ptr (pf_at | ptr)
in '{ 
  m=m, c=c, id= workerid_gen ()
} end // end of [parallel_mc_make]

fn parallel_mc_enque (mc: MC): void = let
(*
  val () = begin
    print "parallel_mc_enque: mc.id = "; print mc.id; print_newline ()
  end
*)
  prval vbox pford12 = parallel_spawn_lockordbox
  prval @(pford1, pford2) = pford12
  val () = mc_enque12 (pford1, pford2 | mc)
in
  pford12 := @(pford1, pford2)
end // end of [parallel_mc_enque]

implement parallel_worker_add_one () = let
(*
  val mc0 = mc_per_thread_get ()
  val () = begin
    print "parallel_worker_add_one: mc0.id = "; print mc0.id; print_newline ()
  end
*)
  val mc = parallel_mc_make ()
(*
  val () = begin
    print "parallel_worker_add_one: mc.id = "; print mc.id; print_newline ()
  end
*)
  val () = parallel_mc_enque (mc)
  val () = pthread_create_detached_lockord12 (
    llam (pf | (*none*)) => let
      val () = mc_per_thread_set (mc)
(*
      val mc = mc_per_thread_get ()
      val () = begin
        print "parallel_mc_enque: mc.id = "; print mc.id; print_newline ()
      end
*)
    in
      worker_fun (pf | mc)
    end
  ) // end of [pthread_create_detached_lockord12]
  val () = nworker_inc ()
in
  // empty
end

implement parallel_worker_add_many (n) = begin
  if n > 0 then begin
    parallel_worker_add_one (); parallel_worker_add_many (n-1)
  end
end // end of [worker_thread_add_many]

(* ****** ****** *)

fn condref_signal (r: ref cond_vt): void =
  let val (vbox pf_cond | p_cond) = ref_get_view_ptr (r) in
    $effmask_all (pthread_cond_signal (!p_cond))
  end

fn mc_lockord1_signal (mc: MC): void = let
  prval vbox pford12 = parallel_spawn_lockordbox
  prval @(pford1, pford2) = pford12
  val (pf1_ticket, pf1_at | ptr1) = lock1_lock (pford1, pford2 | mc.m)
  val () = $effmask_all (condref_signal (mc.c))
  val (pford1 | ()) = lock1_unlock (pf1_ticket, pf1_at | ptr1)
in
  pford12 := @(pford1, pford2)
end

fun parallel_spawn_lockord12 {v:view}
  (pford12: !lockord12 | linclo: () -<lin,cloptr1> (v | void))
  : lockview (v) = let
  val mc_self = mc_per_thread_get ()
(*
  val () = begin
    print "parallel_spawn: 1: mc_self.id = "; print mc_self.id; print_newline ()
  end
*)
  prval @(pford1, pford2) = pford12
  val (pf2_ticket, pf2_at | ptr2) = lock2_lock (pford2 | parallel_nthread)
(*
  val () = begin
    print "parallel_spawn: 2: mc_self.id = "; print mc_self.id; print_newline ()
  end
*)
in
  case+ !ptr2 of
  | ~list_vt_cons (mc, mcs) => let
(*
      val () = begin
        print "parallel_spawn: 1: mc.id = "; print mc.id; print_newline ();
      end
*)
      val () = (!ptr2 := mcs)

      val (pford2 | ()) = lock2_unlock (pf2_ticket, pf2_at | ptr2)
(*
      val () = begin
        print "parallel_spawn: 2: mc.id = "; print mc.id; print_newline ();
      end
*)
      val (pf1_ticket, pf1_at | ptr1) = lock1_lock (pford1, pford2 | mc.m)
(*
      val () = begin
        print "parallel_spawn: 3: mc.id = "; print mc.id; print_newline ();
      end
*)
      val xQ = ptr1->Q; val () = ptr1->Q := 0 // it is dequeued

    in
      if xQ >= 0 then let
        val lock = pthread_uplock_create {v} ()
        val ticket = pthread_upticket_create (lock)
        val mc_self = mc_per_thread_get ()
        val thunk = thunk_make (
          llam () => let
            val (pf | ()) = linclo ()
            val () = cloptr_free (linclo)
            val () = pthread_upticket_upload_and_destroy (pf | ticket)
          in
            mc_lockord1_signal (mc_self)
          end
        ) // end of [thunk_make_linclo]
        val xT = ptr1->T; val () = (ptr1->T := thunkopt_some (thunk))
        val () = condref_signal (mc.c)
        val (pford1 | ()) = lock1_unlock (pf1_ticket, pf1_at | ptr1)
        prval () = (pford12 := @(pford1, pford2))
        val () = assert_errmsg (
          thunkopt_is_none xT, "libats: parallel.dats: parallel_spawn_lockord12\n"
        )
        val () = thunkopt_unnone (xT)
      in
        LOCKVIEWlock lock
      end else let // [xQ = ~1]: upload is not allowed
        val (pford1 | ()) = lock1_unlock (pf1_ticket, pf1_at | ptr1)
        prval () = (pford12 := @(pford1, pford2))
      in
        parallel_spawn_lockord12 (pford12 | linclo)
      end
    end
  | list_vt_nil () => let
      val () = fold@ (!ptr2)
      val (pford2 | ()) = lock2_unlock (pf2_ticket, pf2_at | ptr2)
      prval () = (pford12 := @(pford1, pford2))
      val (pf | ()) = linclo (); val () = cloptr_free (linclo)
    in
      LOCKVIEWview (pf | (*none*))
    end
end // end of [parallel_spawn_lock12]

(* ****** ****** *)

implement parallel_spawn (linclo) = let
  prval vbox pford12 = parallel_spawn_lockordbox
in
  $effmask_all (parallel_spawn_lockord12 (pford12 | linclo))
end

(* ****** ****** *)

fun spawnlock_sync {v:view} {l:addr} (
    pf1_ticket: lock1_unlock_ticket l
  , pf1_at: TQ @ l
  , pford2: !lockord2
  | ptr1: ptr l
  , mc: MC
  , lock: uplock (1, v)
  ) : (lockord1, v | void) = let
  val (pfopt | lockopt) = pthread_uplock_download_try lock
in
  if pthread_uplockopt_is_none lockopt then let
    val xQ = ptr1->Q; val () = if xQ = 1 then ptr1->Q := ~1
    val xT = ptr1->T; val () = ptr1->T := thunkopt_none()
    val (pford1 | ()) = lock1_unlock (pf1_ticket, pf1_at | ptr1)
    val () = begin
      if thunkopt_is_some (xT) then thunk_exec (thunkopt_unsome xT)
      else thunkopt_unnone xT
    end
    val () = pthread_uplockopt_unnone lockopt; prval Some_v pf = pfopt
  in
    (pford1, pf | ())
  end else let
    prval None_v () = pfopt
    val lock = pthread_uplockopt_unsome (lockopt)
  in
    spawnlock_sync_cont (pf1_ticket, pf1_at, pford2 | ptr1, mc, lock)
  end
end // end of [spawnlock_sync]

and spawnlock_sync_cont {v:view} {l:addr} (
    pf1_ticket: lock1_unlock_ticket l
  , pf1_at: TQ @ l
  , pford2: !lockord2
  | ptr1: ptr l
  , mc: MC
  , lock: spawnlock v
  ) : (lockord1, v | void) = let
  val xT = ptr1->T; val () = ptr1->T := thunkopt_none()
in
  if thunkopt_is_some (xT) then let
    val (pford1 | ()) = lock1_unlock (pf1_ticket, pf1_at | ptr1)
    val () = thunk_exec (thunkopt_unsome xT)
    val () = mc_enque12 (pford1, pford2 | mc)
    val (pf1_ticket, pf1_at | ptr1) = lock1_lock (pford1, pford2 | mc.m)
  in
    spawnlock_sync (pf1_ticket, pf1_at, pford2 | ptr1, mc, lock)
  end else let
    val () = thunkopt_unnone xT
    val () = let
      val (vbox pf_cond | p_cond) = ref_get_view_ptr (mc.c)
    in
      cond_wait_lock1 (pford2, pf1_ticket, pf1_at | !p_cond, ptr1)
    end
  in
    spawnlock_sync (pf1_ticket, pf1_at, pford2 | ptr1, mc, lock)
  end
end // end of [spawnlock_sync_cont]

implement parallel_sync (ret) = begin case+ ret of
  | ~LOCKVIEWlock lock => let
      val mc_self = mc_per_thread_get ()
(*
      val () = begin
        print "parallel_sync: mc_self.id = "; print mc_self.id; print_newline ()
      end
*)
      prval vbox pford12 = parallel_spawn_lockordbox
      prval @(pford1, pford2) = pford12
      val () = mc_enque12 (pford1, pford2 | mc_self)
      val (pf1_ticket, pf1_at | ptr1) = lock1_lock (pford1, pford2 | mc_self.m)
      val (pford1, pf | ()) = $effmask_all (
        spawnlock_sync (pf1_ticket, pf1_at, pford2 | ptr1, mc_self, lock)
      )
      prval () = pford12 := @(pford1, pford2)
(*
      val (pf | ()) = pthread_uplock_download (lock)
*)
    in
      (pf | ())
    end
  | ~LOCKVIEWview (pf | (*none*)) => (pf | ())
end // end of [parallel_sync]

(* ****** ****** *)

val () = let
  // for the main thread
  val mc_main = parallel_mc_make ()
  val () = mc_per_thread_set (mc_main)
  val () = nworker_inc ()
in
  print "mc_main.id = "; print mc_main.id; print_newline ()
end

(* ****** ****** *)

(* end of [parallel.dats] *)
