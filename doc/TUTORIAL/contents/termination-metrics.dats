//
//
// Author: Hongwei Xi (August, 2007)
//
//

// [fact] implements the factorial function
fun fact {n:nat} .< n >. (n: int n): Int = if n > 0 then n * fact (n-1) else 1

// [gcd] computes the greates common divisors of two positive integers
fun gcd {m,n:int | m > 0; n > 0} .< m+n >.
  (m: int m, n: int n): [r:nat | 1 <= r; r <= min(m, n)] int r =
  if m > n then gcd (m - n, n)
  else if m < n then gcd (m, n - m)
  else m
// end of [gcd]


// [ack] implements the Ackermann's function
fun ack {m,n:nat} .< m, n >.
  (m: int m, n: int n): Nat =
  if m > 0 then
    if n > 0 then ack (m-1, ack (m, n-1)) else ack (m-1, 1)
  else n+1
// end of [ack]

// mutually recursive functions
fun isEven {n:nat} .< 2*n+2 >. (n: int n): bool =
  if n > 0 then ~(isOdd n) else true
// end of [isEven]

and isOdd {n:nat} .< 2*n+1 >. (n: int n): bool =
  if n > 0 then isEven (n-1) else false
// end of [isOdd]

(* ****** ****** *)

// a simple test
implement main (argc, argv) = let
  val i = 8 and j = 9
  val ack3i = ack (3, i)
  val ack3j = ack (3, j)
  val () = assert (ack3i > 0)
  val () = assert (ack3j > 0)
in
  printf (
    "gcd (ack(3, %i) = %i, ack (3, %i) = %i) = %i\n", @(i, ack3i, j, ack3j, gcd (ack3i, ack3j))
  ) // end of [printf]
end // end of [main]

(* ****** ****** *)

(* end of [termination-metrics.dats] *)
