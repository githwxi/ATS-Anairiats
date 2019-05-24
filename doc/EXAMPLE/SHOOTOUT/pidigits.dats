//
// pidigits.dats -- computing digits of pi
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

// This implementation is only slightly slower
// than the C version given below.

(*

machine: dml.bu.edu

command: pidigits 2500

ATS:	 1.847u 0.002s 0:01.85 99.4%	0+0k 0+0io 0pf+0w
C:	 1.796u 0.002s 0:01.80 99.4%	0+0k 0+0io 0pf+0w

command: pidigits 5000

ATS:	 8.005u 0.028s 0:08.08 99.2%	0+0k 0+0io 0pf+0w
C:	 7.736u 0.031s 0:07.89 98.3%	0+0k 0+0io 0pf+0w

*)

(*

fun g (q: int, r: int, t: int, k: int, n: int, l: int, c:int): void =
  if 4*q+r < (n+1)*t then
    g (10*q, 10*(r-n*t), t, k, (10*(3*q+r)) / t-10*n, l, c-1)
  else g (q*k, (2*q+r)*l, t*l, k+1, (q*(7*k+2)+r*l)/(t*l), l+2, c)

*)

//

staload "libc/SATS/gmp.sats"

fn print_digit (i: int, d: int): void = begin
  print (char_of_int (d + int_of '0')) ;
  if i mod 10 = 0 then printf ("\t:%i\n", @(i))
end

fun g (q: &mpz_vt, r: &mpz_vt, t: &mpz_vt, k: int, n: &mpz_vt, l: int, i: int, N: int): void =
  let
     var x1: mpz_vt? and x2: mpz_vt?

     val () = mpz_init x1 and () = mpz_init x2
     val () = mpz_mul (x1, q, 4) // x1 = 4*q
     val () = mpz_add (x1, r) // x1 = 4*q + r
     val () = mpz_add (x2, n, 1) // x2 = n+1
     val () = mpz_mul (x2, t) // x2 = t * (n+1)
     val cmp = mpz_cmp (x1, x2)
  in
     if cmp < 0 then begin
       print_digit (i, mpz_get_int n);
       mpz_mul (x1, t, n) ; // x1 = n * t
       mpz_sub (x2, r, x1) ; // x2 = r - n * t
       mpz_mul (x2, 10) ; // x2 = 10 (r - n * t)
       mpz_mul (x1, q, 3) ; // x1 = 3 * q
       mpz_add (x1, r) ; // x1 = 3 * q + r
       mpz_mul (x1, 10) ; // x1 = 10 * (3 * q + r)
       mpz_tdiv_q (x1, t) ; // x1 = 10 * (3 * q + r) / t
       mpz_set (r, x2) ;
       mpz_mul (x2, n, 10) ; // x2 = 10 * n
       mpz_sub (n, x1, x2) ; // n = 10 * (3 * q + r) / t - 10 * n
       mpz_mul (q, 10) ; // q = 10 * q
       mpz_clear x1; mpz_clear x2;
       if i < N then g (q, r, t, k, n, l, i+1, N);
     end else begin
       mpz_mul (x1, q, 7 * k + 2) ;
       mpz_mul (x2, r, l) ;
       mpz_add (x1, x2) ; // x1 = q * (7 * k + 2) + r * l
       mpz_mul (t, l) ; // t = t * l
       mpz_tdiv_q (n, x1, t) ;
       mpz_mul (x2, q, 2) ; // x2 = 2 * q
       mpz_add (x2, r) ; // x2 = 2 * q + r
       mpz_mul (r, x2, l) ; // r = (2 * q + r) * l
       mpz_mul (q, k) ;
       mpz_clear x1; mpz_clear x2;
       g (q, r, t, k+1, n, l+2, i, N);
     end
  end

//

fn usage (cmd: string): void =
  prerrf ("Usage: %s [integer]\n", @(cmd))

implement main (argc, argv) = let
  var q: mpz_vt and r: mpz_vt and t: mpz_vt and n: mpz_vt
  val () = if argc <> 2 then (usage (argv.[0]); exit 1)
  val () = assert (argc = 2)
  val N = int1_of argv.[1]
  val () = assert_errmsg_bool1
    (N >= 2, "The input integer needs to be a natural number.\n")
in
  mpz_init_set (q, 1);
  mpz_init_set (r, 0);
  mpz_init_set (t, 1);
  mpz_init_set (n, 3);
  g (q, r, t, 1, n, 3, 1, N);
  mpz_clear q; mpz_clear r; mpz_clear t; mpz_clear n;
  print_newline ();
end // end of [main]

////

/*
** The Computer Language Shootout
** http://shootout.alioth.debian.org/
** contributed by Mike Pall
**
**   gcc -O3 -fomit-frame-pointer -o pidigits pidigits.c -lgmp
*/

#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>

typedef struct ctx_s {
  mpz_t q, r, s, t;	/* Transformation matrix components. */
  mpz_t u, v, w;	/* Temporary numbers. */
  int d, i, n;		/* Counters. */
  char digits[10+1];	/* Accumulated digits for one line. */
} ctx_t;

/* Compose matrix with numbers on the right. */
static void compose_r(ctx_t *c, int bq, int br, int bs, int bt)
{
  mpz_mul_si(c->u, c->r, bs);
  mpz_mul_si(c->r, c->r, bq);
  mpz_mul_si(c->v, c->t, br);
  mpz_add(c->r, c->r, c->v);
  mpz_mul_si(c->t, c->t, bt);
  mpz_add(c->t, c->t, c->u);
  mpz_mul_si(c->s, c->s, bt);
  mpz_mul_si(c->u, c->q, bs);
  mpz_add(c->s, c->s, c->u);
  mpz_mul_si(c->q, c->q, bq);
}

/* Compose matrix with numbers on the left. */
static void compose_l(ctx_t *c, int bq, int br, int bs, int bt)
{
  mpz_mul_si(c->r, c->r, bt);
  mpz_mul_si(c->u, c->q, br);
  mpz_add(c->r, c->r, c->u);
  mpz_mul_si(c->u, c->t, bs);
  mpz_mul_si(c->t, c->t, bt);
  mpz_mul_si(c->v, c->s, br);
  mpz_add(c->t, c->t, c->v);
  mpz_mul_si(c->s, c->s, bq);
  mpz_add(c->s, c->s, c->u);
  mpz_mul_si(c->q, c->q, bq);
}

/* Extract one digit. */
static int extract(ctx_t *c, unsigned int j)
{
  mpz_mul_ui(c->u, c->q, j);
  mpz_add(c->u, c->u, c->r);
  mpz_mul_ui(c->v, c->s, j);
  mpz_add(c->v, c->v, c->t);
  mpz_tdiv_q(c->w, c->u, c->v);
  return mpz_get_ui(c->w);
}

/* Print one digit. Returns 1 for the last digit. */
static int prdigit(ctx_t *c, int y)
{
  c->digits[c->d++] = '0'+y;
  if (++c->i % 10 == 0 || c->i == c->n) {
    c->digits[c->d] = '\0';
    printf("%-10s\t:%d\n", c->digits, c->i);
    c->d = 0;
  }
  return c->i == c->n;
}

/* Generate successive digits of PI. */
static void pidigits(ctx_t *c)
{
  int k = 1;
  c->d = 0;
  c->i = 0;
  mpz_init_set_ui(c->q, 1);
  mpz_init_set_ui(c->r, 0);
  mpz_init_set_ui(c->s, 0);
  mpz_init_set_ui(c->t, 1);
  mpz_init(c->u);
  mpz_init(c->v);
  mpz_init(c->w);
  for (;;) {
    int y = extract(c, 3);
    if (y == extract(c, 4)) {
      if (prdigit(c, y)) return;
      compose_r(c, 10, -10*y, 0, 1);
    } else {
      compose_l(c, k, 4*k+2, 0, 2*k+1);
      k++;
    }
  }
}

int main(int argc, char **argv)
{
  ctx_t c;
  c.n = argc > 1 ? atoi(argv[1]) : 27;
  pidigits(&c);
  return 0;
}

