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

machine: dml.bu.edu
command: time nsieve 12

output:
Primes up to 40960000  2488465
Primes up to 20480000  1299069
Primes up to 10240000   679461

ATS:	  7.433u 0.131s 0:07.61 99.3%	0+0k 0+0io 0pf+0w
C:	  7.337u 0.146s 0:07.58 98.5%	0+0k 0+0io 0pf+0w

*)

%{^

#include "prelude/CATS/array.cats"
#include "libc/CATS/stdlib.cats"

#include "libats/CATS/thunk.cats"

#include "libc/CATS/pthread.cats"
#include "libc/CATS/pthread_locks.cats"

%}

staload "libc/SATS/pthread.sats"
staload "libc/SATS/pthread_locks.sats"

(* ****** ****** *)

staload "libats/SATS/letpar.sats"
staload _(*anonymous*) = "libats/DATS/letpar.dats"

(* ****** ****** *)

dynload "libats/DATS/letpar.dats"

(* ****** ****** *)

//

macdef  tt = int8_of_int (1)
macdef  ff = int8_of_int (0)

//

typedef two = int8

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
end // end of [nsieve]

fn sqrt_int {m:nat} (m: int m): Nat = let
  val m_sqrt = int_of_double (sqrt (double_of m + 0.5))
  val m_sqrt = int1_of_int m_sqrt
  val () = assert (m_sqrt >= 0) // redundant at run-time
in
  m_sqrt
end // end of [sqrt_int]

fn nsieve_mt (m: int): void = let
  val [m:int] m = int1_of_int m
  val () = assert_prerrf (
    m >= 1, "nsieve_mt(%i): argument is illegal; it must be positive.\n", @(m)
  )
  val [l:addr] (pf_gc, pf | A) =
    let fn f (x: &(two?) >> two, _i: natLt m):<clo> void = x := tt in
      array_ptr_make_fun_tsz {two} (m, f, sizeof<two>)
    end
  val m1 = sqrt_int (m)
  val [m1:int] m1 = (if m1 < m then m1 + 1 else m): natLte m
(*
  val m11 = sqrt_int (m1)
  val m11: natLte m1 = if m11 < m1 then m11 + 1 else m1
*)
  val () = sieve_many (pf | A, m1, m1, 2) // find the all the primes upto [m1]

  viewtypedef T = uplock (1, void)
  viewtypedef uplocklst = List_vt (T)

  fun finishoff (locks: uplocklst) = case+ locks of
    | ~list_vt_cons (lock, locks) => let
        val (pf | ()) = pthread_uplock_destroy (lock)
      in
        finishoff (locks)
      end
    | ~list_vt_nil () => ()

  #define NLOCKMAX 1024

  fun main_work {m,m1:nat | m1 <= m} {i:nat} (
      pf: !array_v (two, m, l)
    | A: ptr l
    , m: int m
    , m1: int m1
    , i: int i
    , locks: &uplocklst
    ) : void = begin
    if i < m1 then begin
      if A[i] = tt then let
        var ret: lockview?
        val () = letpar_void (
          llam () => sieve_once_unsafe (A, m, i, i+i), ret
        )
        val () = case+ ret of
          | ~LOCKVIEWlock lock => begin
              locks := list_vt_cons {T} (lock, locks)
            end
          | ~LOCKVIEWview (_(*void*) | (*none*)) => ()
      in
        main_work (pf | A, m, m1, i+1, locks)
      end else begin
        main_work (pf | A, m, m1, i+1, locks)
      end // end of [if]
    end else begin
      // all the works are spawned or finished
    end // end of [if]
  end // end of [main_work]

  var locks: uplocklst = list_vt_nil ()
  val () = main_work (pf | A, m, m1, 2, locks)
  val () = finishoff (locks)

  val count = loop (pf | 2, 0) where {
    fun loop {i:nat}
      (pf: !array_v (two, m, l) | i: int i, c: int):<clo1> int =
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

//

implement main (argc, argv) = let
  var nthread: int = 0
  val () = assert_errmsg (argc >= 2, "Exit: wrong command format!\n")
  val i = int1_of argv.[1]
  val () = assert_errmsg (
    i >= 2, "The input integer needs to be at least 2.\n"
  )
  val () = if argc >= 3 then (nthread := int_of argv.[2])
  val () = letpar_worker_add_many (nthread)
in
  nsieve_mt (10000 << i) ;
  nsieve_mt (10000 << i - 1) ;
  nsieve_mt (10000 << i - 2) ;
end

////

// The Computer Language Shootout
// http://shootout.alioth.debian.org/
// Precedent C entry modified by bearophile for speed and size, 31 Jan 2006
// Compile with:  -O3 -s -std=c99 -fomit-frame-pointer

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned char boolean;

static void nsieve(int m) {
    unsigned int count = 0, i, j;
    boolean * flags = (boolean *) malloc(m * sizeof(boolean));
    memset(flags, 1, m);

    for (i = 2; i < m; ++i)
        if (flags[i]) {
            ++count;
            for (j = i << 1; j < m; j += i)
//                if (flags[j])
                   flags[j] = 0;
    }

    free(flags);
    printf("Primes up to %8u %8u\n", m, count);
}

int main(int argc, char *argv[]) {
  int m = atoi(argv[1]);
  int i;
  for (i = 0; i < 3; i++) nsieve(10000 << (m-i));
  return 0;
}
