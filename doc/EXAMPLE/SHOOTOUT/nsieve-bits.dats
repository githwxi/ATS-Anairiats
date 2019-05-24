//
// nsieve.dats -- naive Sieve of Eratosthenes
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

//

(*

machine: dml.bu.edu
command: time nsieve-bits 11

------

output:

Primes up to 20480000  1299069
Primes up to 10240000   679461
Primes up to  5120000   356244

------

ATS:	2.006u 0.011s 0:02.05 98.0% 0+0k 0+0io 0pf+0w
C:	2.025u 0.026s 0:02.09 97.6% 0+0k 0+0io 0pf+0w

*)


%{^

typedef unsigned int bits;
#define BBITS (sizeof(bits) * 8)
#define BSIZE(x) ((x) / 8 + sizeof(bits))
#define BMASK(x) (1 << ((x) % BBITS))
#define BTEST(p, x) ((p)[(x) / BBITS] & BMASK(x))
#define BFLIP(p, x) (p)[(x) / BBITS] ^= BMASK(x)

static inline
ats_ptr_type
barray_make (ats_int_type n, ats_bool_type b) {
  int bsz; bits *p0;

  bsz = BSIZE(n) ;
  p0 = (bits *)malloc(bsz) ;

  if (b) { memset (p0, 0xff, bsz) ; } else { memset (p0, 0x00, bsz) ; }
  return p0 ;
}

static inline
ats_void_type
barray_free (ats_ptr_type A) { free (A) ; return ; }

static inline
ats_bool_type
barray_get (ats_ptr_type A, ats_int_type i) {
  return BTEST((bits *)A, i) ;
}

static inline
ats_void_type
barray_set (ats_ptr_type A, ats_int_type i, ats_bool_type b) {
  bits mask = BMASK(i) ;
  if (b) ((bits *)A)[i/BBITS] |= mask ; else ((bits *)A)[i/BBITS] &= ~mask ;
  return ;
}

ats_bool_type
barray_test (ats_ptr_type A, ats_int_type i) {
  return BTEST((bits *)A, i) ;
}

static inline
ats_void_type
barray_flip (ats_ptr_type A, ats_int_type i) {
  BFLIP((bits *)A, i) ; return ;
}

%}

absviewt@ype barray (int) // it is linear, so it cannot be leaked

extern fun barray_make {n:nat}
  (n: int n, b: bool): [l:addr] (barray n @ l | ptr l)
  = "barray_make"

extern fun barray_free
  {n:nat} {l:addr} (pf: barray n @ l | p: ptr l): void
  = "barray_free"

extern fun barray_get {n:nat}
  (A: &barray n, i: natLt n): bool = "barray_get"

extern fun barray_set {n:nat}
  (A: &barray n, i: natLt n, b: bool): void = "barray_set"

extern fun barray_test {n:nat}
  (A: &barray n, i: natLt n): bool = "barray_test"

extern fun barray_flip {n:nat}
  (A: &barray n, i: natLt n): void = "barray_flip"

overload [] with barray_get
overload [] with barray_set

//

fn nsieve {m:nat} (m: int m): void = let
  val (pf_A | p_A) = barray_make (m, true)
  var i: Nat = 2 and j: Nat = 0 and count: Nat = 0
  val () = while (i < m) begin
    if barray_get (!p_A, i) then begin
      count := count + 1; j := i + i ;
      while (j < m) begin
        if barray_get (!p_A, j) then barray_flip (!p_A, j);
        j := j + i;
      end // end of [while]
    end ; // end of [if]
    i := i + 1 ;
  end // end of [while]
  val () = barray_free (pf_A | p_A)
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
end // end of [main]

////

/*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
** contributed by Mike Pall
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned int bits;
#define BBITS		(sizeof(bits) * 8)
#define BSIZE(x)	(((x) / 8) + sizeof(bits))
#define BMASK(x)	(1 << ((x) % BBITS))
#define BTEST(p, x)	((p)[(x) / BBITS] & BMASK(x))
#define BFLIP(p, x)	(p)[(x) / BBITS] ^= BMASK(x)

int main(int argc, char **argv)
{
  unsigned int m, sz = 10000 << (argc > 1 ? atoi(argv[1]) : 1);
  bits *primes = (bits *)malloc(BSIZE(sz));
  if (!primes) return 1;
  for (m = 0; m <= 2; m++) {
    unsigned int i, j, count = 0, n = sz >> m;
    memset(primes, 0xff, BSIZE(n));
    for (i = 2; i <= n; i++)
      if (BTEST(primes, i)) {
	count++;
	for (j = i + i; j <= n; j += i)
	  if (BTEST(primes, j)) BFLIP(primes, j);
      }
    printf("Primes up to %8d %8d\n", n, count);
  }
  free(primes);
  return 0;
}

