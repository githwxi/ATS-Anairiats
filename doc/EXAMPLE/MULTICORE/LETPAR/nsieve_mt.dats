//
// Time March 2008
// Author: Hongwei Xi (hwxi @ cs.bu.edu)
//
// This is an effort for parallelizing a program I wrote
// earlier last year.
//
// On csa2.bu.edu (8p) and csa3.bu.edu (8p), the real-time
// efficiency is doubled.
//

//
// nsieve.dats -- naive Sieve of Eratosthenes
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(*

command: time nsieve 12

output:
Primes up to 40960000  2488465

*)

%{^

#include "thunk.cats"
#include "pthread.cats"
#include "pthread_locks.cats"

#include "libc/CATS/math.cats"

%}

staload "pthread.sats"
staload "pthread_locks.sats"

(* ****** ****** *)

staload "parallel.sats"
dynload "parallel.dats"

(* ****** ****** *)

// staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

typedef two = bool
macdef  tt = true
macdef  ff = false

(* ****** ****** *)

extern fun sieve_once {m,limit:nat | limit <= m} {i,j:nat} {l:addr}
  (pf: !array_v (two, m, l) |
   A: ptr l, limit: int limit, i: int i, j: int j): void
  = "sieve_once_safe"

implement sieve_once (pf | A, limit, i, j) = begin
  if (j < limit) then begin
    (if A[j] <> ff then A[j] := ff; sieve_once (pf | A, limit, i, j+i))
  end // end of [if]
end // end of [sieve_once]

extern fun sieve_once_unsafe (A: Ptr, limit: int, i: int, j: int): void
  = "sieve_once_safe"

fun sieve_many {m,m1,m2:nat | m1 <= m; m2 <= m} {i:nat} {l:addr}
  (pf: !array_v (two, m, l) | A: ptr l, m1: int m1, m2: int m2, i: int i)
  : void = begin
  if i < m1 then begin
    if A[i] = tt then sieve_once (pf | A, m2, i, i+i);
    sieve_many (pf | A, m1, m2, i+1)
  end // end of [if]
end // end of [sieve_many]

(* ****** ****** *)

local

staload M = "libc/SATS/math.sats"

in

fn sqrt_int {m:nat} (m: int m): Nat = let
  val m_sqrt = int_of_double ($M.sqrt (double_of m + 0.5))
  val m_sqrt = int1_of_int (m_sqrt)
  val () = assert (m_sqrt >= 0) // redundant at run-time
in
  m_sqrt
end // end of [sqrt_int]

end // end of [local]

(* ****** ****** *)

implement{a}
array_ptr_initialize_fun
  {n} {f:eff} (base, asz, f) = let
//
  typedef fun_t = (sizeLt n, &(a?) >> a) -<f> void
  typedef fun1_t = (!unit_v | sizeLt n, &(a?) >> a, !ptr) -<f> void
  val f1 = coerce (f) where {
    extern castfn coerce (f: fun_t):<> fun1_t
  } // end of [val]
//
  prval pfu = unit_v ()
  val () = array_ptr_initialize_funenv_tsz
    {a} {unit_v} {ptr} (pfu | base, asz, f1, sizeof<a>, null)
  prval unit_v () = pfu
//
in
  // empty
end // end of [array_ptr_initialize_fun_tsz]

fun{a:t@ype}
array_ptr_make_fun {m:nat} (
  m: int m, f: (sizeLt m, &(a?) >> a) -> void
) :[l:agz] (
  free_gc_v (a, m, l), array_v (a, m, l) | ptr l
) = let
  val asz = size1_of_int1 (m)
  val (pfgc, pfat | p) = array_ptr_alloc_tsz {a} (asz, sizeof<a>)
  val () = array_ptr_initialize_fun<a> (!p, asz, f)
in
  (pfgc, pfat | p)
end // end of [array_ptr_make_fun]

fn nsieve_mt
  (m: int): void = let
  val [m:int] m = int1_of_int m
  val () = assert_prerrf_bool1 (
    m >= 1, "nsieve_mt(%i): argument is illegal; it must be positive.\n", @(m)
  )
  val [l:addr] (pf_gc, pf | A) = let
    fn f (_: sizeLt m, x: &(two?) >> two): void = x := tt
  in
    array_ptr_make_fun<two> (m, f)
  end // end of [val]
  val m1 = sqrt_int (m)
  val [m1:int] m1 = (if m1 < m then m1 + 1 else m): natLte m
(*
  val m11 = sqrt_int (m1)
  val m11: natLte m1 = if m11 < m1 then m11 + 1 else m1
*)
  val () = sieve_many (pf | A, m1, m1, 2) // find the all the primes upto [m1]

  viewtypedef T = spawnlock (unit_v)
  viewtypedef spawnlocklst = List_vt (T)

  fun finishoff (locks: spawnlocklst): void = case+ locks of
    | ~list_vt_cons (lock, locks) => let
        val (unit_v () | ()) = spawnlock_download (lock)
      in
        finishoff (locks)
      end
    | ~list_vt_nil () => ()

  fun main_work {m,m1:nat | m1 <= m} {i:nat} (
      pf: !array_v (two, m, l)
    | A: ptr l
    , m: int m
    , m1: int m1
    , i: int i
    , locks: &spawnlocklst
    ) : void = begin
    if i < m1 then begin
      if A[i] = tt then let
        val ret = parallel_spawn {unit_v} (
          llam () => (sieve_once_unsafe (A, m, i, i+i); (unit_v | ()))
        )
        val () = case+ ret of // postponing synchronization
          | ~LOCKVIEWlock lock => begin
              locks := list_vt_cons {T} (lock, locks)
            end
          | ~LOCKVIEWview (unit_v () | (*none*)) => ()
      in
        main_work (pf | A, m, m1, i+1, locks)
      end else begin
        main_work (pf | A, m, m1, i+1, locks)
      end // end of [if]
    end else begin
      // all the works are spawned or finished
    end // end of [if]
  end // end of [main_work]

  var locks: spawnlocklst = list_vt_nil ()
  val () = main_work (pf | A, m, m1, 2, locks)
  val () = finishoff (locks)

  val count = loop (pf | 2, 0) where {
    fun loop {i:nat}
      (pf: !array_v (two, m, l) | i: int i, c: int):<cloptr1> int =
      if i < m then begin
        if A[i] = tt then loop (pf | i+1, c+1) else loop (pf | i+1, c)
      end else begin
        c // return value
      end
  } // end of [where]
in
  array_ptr_free {two} (pf_gc, pf | A) ;
  printf ("Primes up to %8i %8i\n", @(m, count))
end // end of [nsieve]

(* ****** ****** *)

implement main (argc, argv) = let
  var nthread: int = 0
  val () = assert_errmsg_bool1 (
    argc >= 2, "Exit: wrong command format!\n"
  )
  val i = int1_of argv.[1]
  val () = assert_errmsg_bool1 (
    i >= 2, "The input integer needs to be at least 2.\n"
  )
  val () = if argc >= 3 then (nthread := int_of argv.[2])
  val () = parallel_worker_add_many (nthread-1)
  val () = printf ("There are now [%i] workers.", @(nthread))
  val () = print_newline ()
in
  nsieve_mt (i) ;
end

(* ****** ****** *)

(* end of [nsieve_mt.dats] *)
