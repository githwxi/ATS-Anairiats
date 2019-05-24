//
// partial-sums.dats: computing partial sums of various series
//
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(*

machine: dml.bu.edu
command: partial-sums 2500000

ATS:	4.656u 0.002s 0:04.77 97.4%	0+0k 0+0io 0pf+0w
C:	4.658u 0.003s 0:04.69 99.1%	0+0k 0+0io 0pf+0w
OCAML:	5.508u 0.017s 0:05.58 98.7%	0+0k 0+0io 0pf+0w

*)

staload M = "libc/SATS/math.sats"

fun loop1 (n: int, i: int, sum: double): double =
  if i < n then loop1 (n, i+1, sum + $M.pow(2.0 / 3.0, double_of i)) else sum

fun loop2 (n: int, i: int, sum: double): double =
  if i < n then loop2 (n, i+1, sum + 1.0 / $M.sqrt (double_of i)) else sum

fun loop3 (n: int, i: int, sum: double): double =
  if i < n then
    let val f = double_of i in loop3 (n, i+1, sum + 1.0 / (f * (f + 1.0))) end
  else sum

fun loop4 (n: int, i: int, sum: double): double =
  if i < n then let
    val f = double_of i; val sf = $M.sin f
  in
    loop4 (n, i+1, sum + 1.0 / ((f * f * f) * (sf * sf)))
  end else sum

fun loop5 (n:int, i: int, sum: double): double =
  if i < n then let
    val f = double_of i; val cf = $M.cos f
  in
    loop5 (n, i+1, sum + 1.0 / ((f * f * f) * (cf * cf)))
  end else sum

fun loop6 (n: int, i: int, sum: double): double =
  if i < n then loop6 (n, i+1, sum + 1.0 / double_of i)
  else sum

fun loop7 (n: int, i: int, sum: double): double =
  if i < n then
    let val f = double_of i in loop7 (n, i+1, sum + 1.0 / (f * f)) end
  else sum

fun loop8 (n: int, i: int, sgn: double, sum: double): double =
  if i < n then
    loop8 (n, i+1, ~sgn, sum +  sgn / double_of i)
  else sum

fun loop9 (n: int, i: int, sgn: double, sum: double): double =
  if i < n then
    loop9 (n, i+1, ~sgn, sum +  sgn / (2.0 * double_of i - 1.0))
  else sum

//

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val n = int_of argv.[1]
in
  printf ("%.9f\t(2/3)^k", @(loop1 (n, 0, 0.0)));
  print_newline ();
  printf ("%.9f\tk^-0.5", @(loop2 (n, 1, 0.0)));
  print_newline ();
  printf ("%.9f\t1/k(k+1)", @(loop3 (n, 1, 0.0)));
  print_newline ();
  printf ("%.9f\tFlint Hills", @(loop4 (n, 1, 0.0)));
  print_newline ();
  printf ("%.9f\tCookson Hills", @(loop5 (n, 1, 0.0)));
  print_newline ();
  printf ("%.9f\tHarmonic", @(loop6 (n, 1, 0.0)));
  print_newline ();
  printf ("%.9f\tRiemann Zeta", @(loop7 (n, 1, 0.0)));
  print_newline ();
  printf ("%.9f\tAlternating Harmonic", @(loop8 (n, 1, 1.0, 0.0)));
  print_newline ();
  printf ("%.9f\tGregory", @(loop9 (n, 1, 1.0, 0.0)));
  print_newline ();
end // end of [main]

////

/*
** The Computer Language Shootout
** http://shootout.alioth.debian.org/
** contributed by Mike Pall
** de-optimized by Isaac Gouy
**
** compile with:
**   gcc -O3 -fomit-frame-pointer -ffast-math -o partialsums partialsums.c -lm
**   Adding -march=<yourcpu> may help, too.
**   On a P4/K8 or later try adding: --march=<yourcpu> -mfpmath=sse -msse2
*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main(int argc, char **argv)
{
  int k, n = atoi(argv[1]);
  double sum, a;

/*
** Yes, I (Mike Pall) tried using a double as a primary or secondary loop variable.
** But the x86 ABI requires a cleared x87 FPU stack before every call
** (e.g. to sin()) which nullifies any performance gains.
**
** Combining all loops does not pay off because the x87 FPU has to shuffle
** stack slots and/or runs out of registers. This may not be entirely true
** for SSE2 with fully inlined FPU code (-ffast-math required). Dito for
** other CPUs with a register-based FPU and a sane FP ABI.
**
** Auto vectorization may be a bit easier with separate loops, too.
*/

#define kd ((double)k)

  sum = 0.0;
  for (k = 0; k <= n; k++) sum += pow(2.0/3.0, kd);
  printf("%.9f\t(2/3)^k\n", sum);

  sum = 0.0;
  for (k = 1 ; k <= n; k++) sum += 1/sqrt(kd);  /* aka pow(kd, -0.5) */
  printf("%.9f\tk^-0.5\n", sum);

  sum = 0.0;
  for (k = 1; k <= n; k++) sum += 1.0/(kd*(kd+1.0));
  printf("%.9f\t1/k(k+1)\n", sum);

  sum = 0.0;
  for (k = 1; k <= n; k++) {
    double sk = sin(kd);
    sum += 1.0/(kd*kd*kd*sk*sk);
  }
  printf("%.9f\tFlint Hills\n", sum);

  sum = 0.0;
  for (k = 1; k <= n; k++) {
    double ck = cos(kd);
    sum += 1.0/(kd*kd*kd*ck*ck);
  }
  printf("%.9f\tCookson Hills\n", sum);

  sum = 0.0;
  for (k = 1; k <= n; k++) sum += 1.0/kd;
  printf("%.9f\tHarmonic\n", sum);

  sum = 0.0;
  for (k = 1; k <= n; k++) sum += 1.0/(kd*kd);
  printf("%.9f\tRiemann Zeta\n", sum);

  sum = 0.0; a = -1.0;
  for (k = 1; k <= n; k++) sum += (a = -a)/kd;
  printf("%.9f\tAlternating Harmonic\n", sum);

  sum = 0.0;  a = -1.0;
  for (k = 1; k <= n; k++) sum += (a = -a)/(2.0*kd - 1.0);
  printf("%.9f\tGregory\n", sum);

  return 0;
}

////

(* partialsums.ml
 *
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Christophe TROESTLER
 *)

let n = try int_of_string (Array.get Sys.argv 1) with _ -> 25000

let () =
  let sum = ref 0.0 in
  for k = 0 to n do sum := !sum +. (2. /. 3.)**(float k) done;
  Printf.printf "%.9f\t(2/3)^k\n" !sum;

  sum := 0.0;
  for k = 1 to n do sum := !sum +. 1. /. sqrt(float k) done;
  Printf.printf "%.9f\tk^-0.5\n" !sum;

  sum := 0.0;
  for k = 1 to n do let k = float k in sum := !sum +. 1.0/.(k*.(k+.1.0)) done;
  Printf.printf "%.9f\t1/k(k+1)\n" !sum;

  sum := 0.0;
  for k = 1 to n do
    let k = float k in let  sk = sin(k) in
    sum := !sum +. 1.0 /. (k *. k *. k *. sk *. sk)
  done;
  Printf.printf "%.9f\tFlint Hills\n" !sum;

  sum := 0.0;
  for k = 1 to n do
    let k = float k in let ck = cos(k) in
    sum := !sum +. 1.0 /. (k *. k *. k *. ck *. ck)
  done;
  Printf.printf "%.9f\tCookson Hills\n" !sum;

  sum := 0.0;
  for k = 1 to n do sum := !sum +. 1. /. float k done;
  Printf.printf "%.9f\tHarmonic\n" !sum;

  sum := 0.0;
  for k = 1 to n do let k = float k in sum := !sum +. 1. /. (k *. k) done;
  Printf.printf "%.9f\tRiemann Zeta\n" !sum;

  sum := 0.0;  let a = ref(-1.0) in
  for k = 1 to n do a := -. !a; sum := !sum +. !a /. float k done;
  Printf.printf "%.9f\tAlternating Harmonic\n" !sum;

  sum := 0.0;  a := -1.0;
  for k = 1 to n do a := -. !a; sum := !sum +. !a /. (2. *. float k -. 1.) done;
  Printf.printf "%.9f\tGregory\n" !sum

