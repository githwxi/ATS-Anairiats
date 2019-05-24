//
// ProjectEuler: Problem 7
// Finding the 10001st prime number
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX:
// This one is fully verified if a primality test is _assumed_ to be correct!
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)

absprop PRIME (p: int, b: bool)
// PRIME (p, true): [p] is a prime
// PRIME (p, false): [p] is not a prime

(* ****** ****** *)
//
// HX-2010-09-20: not sure how to handle this one yet
//
extern
fun isprime {n:nat} (n: int n):<> [b:bool] (PRIME (n, b) | bool b) = "isprime"

(* ****** ****** *)

dataprop NPRIME (int, int) =
  | NPRIMEbas (0, 0) of ()
  | {n:nat} {np:nat}
    NPRIMEind0 (n+1, np) of (NPRIME (n, np), PRIME (n, false))
  | {n:nat} {np:nat}
    NPRIMEind1 (n+1, np+1) of (NPRIME (n, np), PRIME (n, true))
// end of [NPRIME]

(* ****** ****** *)

fun search {np:nat} (np: int np)
  : [n:nat] (NPRIME (n, np), PRIME (n, true) | int n) = let
  fun loop {n:nat}
    {k:nat | k <= np}
    (pf: NPRIME (n, np-k) | n: int n, k: int k)
    : [n:nat] (NPRIME (n, np), PRIME (n, true) | int n) = let
    val (pfres | res) = isprime (n)
  in
    if res then (
      if k > 0 then let
        prval pf = NPRIMEind1 (pf, pfres) in loop (pf | n+1, k-1)
      end else
        (pf, pfres | n)
      // end of [if]
    ) else let
      prval pf = NPRIMEind0 (pf, pfres) in loop (pf | n+1, k)
    end // end of [if]
  end // end of [loop]
in
  loop (NPRIMEbas | 0, np)
end // end of [search]

(* ****** ****** *)

implement
main (argc, argv) = () where {
//
  val (_, _ | ans) = search (10000)
  val () = assert_errmsg (ans = 104743, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
//
} // end of [main]

(* ****** ****** *)

extern
fun isprime0 (n: int): bool = "isprime"
implement
isprime0 (n) = let
  val r = int_of (sqrt (n + 0.5))
  fun loop (p: int):<cloref1> bool =
    if p <= r then
      (if (n mod p > 0) then loop (p+1) else false)
    else true
  // end of [loop]
in
  if n >= 2 then loop (2) else false
end // end of [isprime0]

(* ****** ****** *)

(* end of [problem7-hwxi2.dats] *)
