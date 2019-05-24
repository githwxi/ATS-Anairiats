//
// recursive.dats -- some recursive functions
// The Great Computer Language Shootout
// http://shootout.alioth.debian.org/
//
// by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(*

machine: dml.bu.edu
command: recursive 11

ATS:	 3.921u 0.001s 0:03.97 98.7% 0+0k 0+0io 0pf+0w
C:	 4.450u 0.001s 0:04.46 99.7% 0+0k 0+0io 0pf+0w
OCAML:	 8.233u 0.013s 0:08.27 99.6% 0+0k 0+0io 0pf+0w

*)

//
// This implementation even beats a corresponding
// C version by a handy margin (about 5%)
//

fun ack (x: int, y: int): int =
  if x = 0 then y + 1
  else if y = 0 then ack (x-1, 1)
  else ack (x-1, ack (x, y-1))

fun fib (n: int): int = if n < 2 then 1 else fib(n-2) + fib(n-1)

fun fib_fp (n: double): double =
 if (n < 2.0) then 1.0 else fib_fp(n - 2.0) + fib_fp(n - 1.0)

fun tak (x: int, y: int, z: int): int =
  if y < x then tak (tak (x-1, y, z), tak (y-1, z, x),  tak (z-1, x, y)) else z

fun tak_fp (x: double, y: double, z: double): double =
  if y < x then
    tak_fp (tak_fp (x-1.0, y, z), tak_fp (y-1.0, z, x), tak_fp (z-1.0, x, y))
  else z

//

implement main (argc, argv) = let
  val () = assert_errmsg_bool1
    (argc = 2, "Exit: wrong command format!\n")
  val n = int_of argv.[1] - 1
in
  printf ("Ack(3,%d): %d\n", @(n+1, ack (3, n+1)));
  printf ("Fib(%.1f): %.1f\n", @(28.0 + double_of n, fib_fp (28.0 + double_of n)));
  printf ("Tak(%d,%d,%d): %d\n", @(3*n, 2*n, n, tak (3*n, 2*n, n)));
  printf ("Fib(3): %d\n", @(fib 3));
  printf ("Tak(3.0,2.0,1.0): %.1f\n", @(tak_fp (3.0, 2.0, 1.0)))
end // end of [main]

////

(* recursive.ml
 *
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Christophe TROESTLER
 *)

let rec ack x y =
  if x = 0 then y + 1
  else if y = 0 then ack (x-1) 1
  else ack (x-1) (ack x (y-1))

let rec fib n = if n < 2 then 1 else fib(n-2) + fib(n-1)

let rec fib_fp n =
 if n = 0. || n = 1. then 1. else fib_fp(n -. 2.) +. fib_fp(n -. 1.)

let rec tak x y z =
  if y < x then tak (tak (x-1) y z) (tak (y-1) z x) (tak (z-1) x y) else z

let rec tak_fp x y z =
  if y >= x then z else
    tak_fp (tak_fp (x -. 1.) y z) (tak_fp (y -. 1.) z x) (tak_fp (z -. 1.) x y)


let () =
  let n = int_of_string(Array.get Sys.argv 1) - 1 in
  Printf.printf "Ack(3,%d): %d\n" (n+1) (ack 3 (n+1));
  Printf.printf "Fib(%.1f): %.1f\n" (28. +. float n) (fib_fp (28. +. float n));
  Printf.printf "Tak(%d,%d,%d): %d\n" (3*n) (2*n) n (tak (3*n) (2*n) n);
  Printf.printf "Fib(3): %d\n" (fib 3);
  Printf.printf "Tak(3.0,2.0,1.0): %.1f\n" (tak_fp 3.0 2.0 1.0)

////

/*
 * The Computer Language Shootout
 * http://shootout.alioth.debian.org/

 * contributed by bearophile, Jan 24 2006
 * modified by wolfjb, Feb 28 2007
 */
#include <stdio.h>

int ack(int x, int y) {
  if (x == 0) {
    return y + 1;
  }

  return ack(x - 1, ((y | 0) ? ack(x, y - 1) : 1));
}

int fib(int n) {
  if (n < 2) {
    return 1;
  }
  return fib(n - 2) + fib(n - 1);
}

double fibFP(double n) {
  if (n < 2.0) {
    return 1.0;
  }
  return fibFP(n - 2.0) + fibFP(n - 1.0);
}

int tak(int x, int y, int z) {
  if (y < x) {
    return tak(tak(x - 1, y, z), tak(y - 1, z, x), tak(z - 1, x, y));
  }
  return z;
}

double takFP(double x, double y, double z) {
    if (y < x)
        return takFP( takFP(x-1.0, y, z), takFP(y-1.0, z, x), takFP(z-1.0, x, y) );
    return z;
}

int main(int argc, char ** argv) {
  int n = atoi(argv[1]) - 1;

  printf("Ack(3,%d): %d\n", n + 1, ack(3, n+1));
  printf("Fib(%.1f): %.1f\n", 28.0 + n, fibFP(28.0+n));
  printf("Tak(%d,%d,%d): %d\n", 3 * n, 2 * n, n, tak(3*n, 2*n, n));
  printf("Fib(3): %d\n", fib(3));
  printf("Tak(3.0,2.0,1.0): %.1f\n", takFP(3.0, 2.0, 1.0));

  return 0;
}

////

// The Computer Language Shootout
// http://shootout.alioth.debian.org/
// by bearophile, Jan 24 2006
// converted to C++ by Greg Buchholz
// modified by Paul Kitchin

#include <iomanip>
#include <iostream>
#include <sstream>

template < class N >
N Ack(N x, N y) __attribute__((fastcall, const, nothrow));

template < class N >
N Ack(N x, N y)
{
   return __builtin_expect(x == 0, 0) ? y + 1 : ((y == 0) ? Ack(x - 1, 1) : Ack(x - 1, Ack(x, y - 1)));
}

template < class N >
N Fib(N n) __attribute__((fastcall, const, nothrow));

template < class N >
N Fib(N n)
{
   return __builtin_expect(n < 2, 0) ? 1 : Fib(n - 2) + Fib(n - 1);
}

template < class N >
N Tak(N x, N y, N z) __attribute__((fastcall, const, nothrow));

template < class N >
N Tak(N x, N y, N z)
{
    return __builtin_expect(y < x, 0) ? Tak(Tak(x - 1, y, z), Tak(y - 1, z, x), Tak(z - 1, x, y)) : z;
}

int main(int argc, char * * argv)
{
   if (argc != 2)
   {
      std::cerr << "usage: nsieve <n>\n";
      return 1;
   }
   int n;
   {
      std::istringstream convertor(argv[1]);
      if (!(convertor >> n) || !convertor.eof())
      {
         std::cerr << "usage: nsieve <n>\n";
         std::cerr << "   n must be an integer\n";
         return 1;
      }
   }
   std::cout << std::setprecision(1) << std::setiosflags(std::ios_base::fixed);
   std::cout << "Ack(3," << n << "): " << Ack(3, n) << '\n';
   std::cout << "Fib(" << (27.0 + n) << "): " << Fib(27.0 + n) << '\n';
   --n;
   std::cout << "Tak(" << (3 * n) << ',' << (2 * n) << ',' << n << "): " << Tak(3 * n, 2 * n, n) << '\n';
   std::cout << "Fib(3): " << Fib(3) << '\n';
   std::cout << "Tak(3.0,2.0,1.0): " << Tak(3.0, 2.0, 1.0) << '\n';
}
