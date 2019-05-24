//
//
// code for illustration in lazy-evaluation.html
//
//

(* ****** ****** *)

staload "prelude/DATS/lazy.dats"

(* ****** ****** *)

(*

// this datatype is declared in "prelude/SATS/lazy.sats"

datatype stream_con (a:t@ype+) =
  | stream_nil (a) | stream_cons (a) of (a, stream a)
where stream (a:t@ype) = lazy (stream_con a)

*)

#define nil stream_nil
#define cons stream_cons
#define :: stream_cons

(* ****** ****** *)

typedef N2 = [n:int | n >= 2] int n
val N2s: stream N2 = from 2 where {
  fun from (n: N2):<!laz> stream N2 = $delay (n :: from (n+1))
}

fun sieve
  (ns: stream N2):<!laz> stream N2 = let
  // [val-] means no warning message from the compiler
  val- n :: ns = !ns
in
  $delay (n :: sieve (stream_filter_cloref<N2> (ns, lam x => x nmod n > 0)))
end // end of [sieve]

val primes: stream N2 = sieve N2s

// find the nth prime
fn nprime {n: pos} (n: int n): N2 = stream_nth (primes, n-1)

(* ****** ****** *)

val one = int64_of_int 1

val // the following values are defined mutually recursively
rec fibs_1: stream int64 = $delay (one :: fibs_2) // fib1, fib2, ...
and fibs_2: stream int64 = $delay (one :: fibs_3) // fib2, fib3, ...
and fibs_3: stream int64 = ( // fib3, fib4, ...
  stream_map2_fun<int64,int64><int64> (fibs_1, fibs_2, lam (x, y) => x + y)
)
// find the nth Fibonacci number
fn nfib {n:pos} (n: int n): int64 = stream_nth (fibs_1, n-1)

(* ****** ****** *)

implement main (argc, argv) = begin

printf ("prime 1    = %i\n", @(nprime 1)) ;
printf ("prime 10   = %i\n", @(nprime 10)) ;
printf ("prime 100  = %i\n", @(nprime 100)) ;
printf ("prime 1000 = %i\n", @(nprime 1000)) ;
printf ("prime 10000 = %i\n", @(nprime 10000)) ;

print ("nfib 10 = "); print (nfib 10); print_newline ();
print ("nfib 20 = "); print (nfib 20); print_newline ();
print ("nfib 30 = "); print (nfib 30); print_newline ();
print ("nfib 40 = "); print (nfib 40); print_newline ();
print ("nfib 50 = "); print (nfib 50); print_newline ();

end // end of [main]

(* ****** ****** *)

(* end of [lazy-evaluation.dats] *)

