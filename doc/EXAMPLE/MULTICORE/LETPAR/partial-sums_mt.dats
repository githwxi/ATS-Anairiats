//
// partial-sums.dats: computing partial sums of various series
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: March 2008
//

(* ****** ****** *)

staload
M = "libc/SATS/math.sats"
%{^
#include "libc/CATS/math.cats"
%}

(* ****** ****** *)

%{^

#include "thunk.cats"
#include "pthread.cats"
#include "pthread_locks.cats"

%}

staload "pthread.sats"
staload "pthread_locks.sats"
staload "parallel.sats"

(* ****** ****** *)

dynload "parallel.dats"

(* ****** ****** *)

fun loop1 (n: int, i: int, sum: double): double =
  if i < n then loop1 (n, i+1, sum + $M.pow(2.0 / 3.0, double_of i)) else sum

#define NLOOP1SPLIT 2048
fun loop1_mt (n: int, i: int): double = let
  val ni = n - i
in
  if ni > NLOOP1SPLIT then let
    val ni2 = i + (ni / 2)

    val par sum1 = loop1_mt (n, ni2) and sum2 = loop1_mt (ni2, i)
  in
    sum1 + sum2
  end else begin
    loop1 (n, i, 0.0)
  end
end // end of [loop1_mt]

(* ****** ****** *)

implement main (argc, argv) = let
  var nthread: int = 0
  val () = assert_errmsg_bool1 (argc >= 2, "Exit: wrong command format!\n")
  val n = int_of argv.[1]
  val () = if argc >= 3 then (nthread := int_of argv.[2])
  val () = parallel_worker_add_many (nthread-1)

  val res1 = loop1_mt (n, 0)

in
  printf ("%.9f\t(2/3)^k", @(res1)); print_newline ();
end // end of [main]

(* ****** ****** *)

(* end of [partial-sums_mt.dats] *)
