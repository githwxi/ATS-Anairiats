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

macdef  true = int8_of_int 1
macdef false = int8_of_int 0

typedef bool = int8

fn nsieve {m:nat} (m: int m): void = let
  val m_sz = size1_of_int1 m
  val [l:addr] (pf_gc, pf | A) =
    array_ptr_alloc_tsz {bool} (m_sz, sizeof<bool>)
  var _true: bool = true
  val () = array_ptr_initialize_elt_tsz {bool} (!A, m_sz, _true, sizeof<bool>)

  fun loop1
    (pf: !array_v (bool, m, l) | i: Nat, j: Nat):<cloptr1> void =
    if (j < m) then
      (if A[j] = true then A[j] := false; loop1 (pf | i, j+i))
    // end of [if]
  // end of [loop1]

  fun loop2 (pf: !array_v (bool, m, l) | i: Nat, c: Nat):<cloptr1> Nat =
    if i < m then
      if A[i] = true then (loop1 (pf | i, i+i); loop2 (pf | i+1, c+1))
      else loop2 (pf | i+1, c)
    else c
  // end of [loop2]

  val count = loop2 (pf | 2, 0)

  val () = array_ptr_free {bool?} (pf_gc, pf | A)
in
  printf ("Primes up to %8i %8i\n", @(m, count))
end // end of [nsieve]

fn nsieve (m: int): void = let
  val m = int1_of_int m
  val () = begin
    if (m < 0) then prerrf ("Exit: nsieve(%i) failed.\n", @(m))
  end
  val () = assert (m >= 0)
in
  nsieve m
end // end of [nsieve]

//

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val i = int1_of argv.[1]
  val () = assert_errmsg_bool1
    (i >= 2, "The input integer needs to be at least 2.\n")
in
  nsieve (10000 << i) ;
  nsieve (10000 << i - 1) ;
  nsieve (10000 << i - 2) ;
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
