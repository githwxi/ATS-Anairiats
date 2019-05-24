//
// ProjectEuler: Problem 60
// Finding five primes of minimal sum such that the concatenation of any two of them
// is also a prime
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX: the search take about 20 seconds on wildwest.bu.edu; a bit too long :(
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/list.dats"

(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)

fun isqrt (x: int): int = int_of (sqrt (x+0.5))

fun isprime
  (x: int): bool = let
  val x2 = isqrt (x)
  fun loop (p: int):<cloref1> bool =
    if p <= x2 then
      (if x mod p = 0 then false else loop (p+1))
    else true // end of [if]
in
  if x >= 2 then loop (2) else false
end // end of [isprime]

(* ****** ****** *)

#define TSZ 1000000
val theTable = array_make_elt<int> (TSZ, 0)
val () = loop (0) where {
  fun loop (n: natLte TSZ): void =
    if n < TSZ then let
      val () = if isprime (n) then theTable[n] := 1
    in
      loop (n+1)
    end // end of [if]
} // end of [val]

fun isprime1
  (x: natLt TSZ): bool = theTable[x] >= 1
// end of [isprime1]

fun isprime2
  (x: int): bool = let
  val x2 = isqrt (x)
  val x2 = uint_of_int (x2)
  val x2 = uint1_of_uint (x2)
  val x2 = int1_of_uint1 (x2)
  val () = assert_errmsg (x2 < TSZ, #LOCATION)
  fun loop {p:nat} (p: int p):<cloref1> bool =
    if p <= x2 then
      if isprime1 (p) andalso (x mod p = 0) then false else loop (p+1)
    else true // end of [if]
in
  if x >= 2 then loop (2) else false
end // end of [isprime]

fun isprime3
  (x: int): bool = let
  val x = uint_of_int (x)
  val x = uint1_of_uint (x)
  val x = int1_of_uint1 (x)
in
  if x < TSZ then isprime1 (x) else isprime2 (x)
end // end of [isprime3]

(* ****** ****** *)

fun getNextPrime (x: int): int =
  if isprime3 (x) then x else getNextPrime (x+1)

(* ****** ****** *)

fun concat
  (x1: int, x2: int): int = loop (x2, x1, x2) where {
  fun loop (x: int, res: int, x2: int): int =
    if x > 0 then loop (x/10, 10*res, x2) else res + x2
  // end of [loop]
} // end of [concat]

(* ****** ****** *)

typedef intlst = List (int)
#define nil list_nil
#define cons list_cons

fun print_intlst
  (xs: intlst): void = loop (xs, 0) where {
  fun loop (xs: intlst, n: int): void =
    case+ xs of
    | cons (x, xs) => let
        val () = (if n > 0 then print ","; print x) in loop (xs, n+1)
      end // end of [cons]
    | nil () => ()
} // end of [print_intlist]

fun test1 (x: int, xs: intlst): bool =
  case+ xs of
  | cons (x1, xs1) =>
      if isprime3 (x \concat x1) then
        if isprime3 (x1 \concat x) then test1 (x, xs1) else false
      else false
  | nil () => true
// end of [test1]

fun test2 (x: int, xs: intlst): bool = isprime3 x andalso test1 (x, xs) 

(* ****** ****** *)

#define N 5

//
// Finding N primes such that the sum of them is less than SUM
// and the concat of any two of them is a prime
//
fn* search
  (SUM: int, xs: intlst, n: int, sum: int): int = let
in
  if n < N then let
    val x = (case+ xs of cons (x, _) => x | nil () => 2): int
  in
    search2 (SUM, xs, x+1, n, sum)
  end else let
    val () = (print "search: xs = "; print_intlst xs; print_newline ())
    val SUM = sum
    val sum = search (SUM-1, nil, 0, 0)
  in
    if sum >= 0 then sum else SUM
  end
end // end of [search]

and search2
  (SUM: int, xs: intlst, x: int, n: int, sum: int): int = let
  val x = getNextPrime (x)
  val sum1 = sum + (N-n)*x
in
  if sum1 < SUM then (
    if test1 (x, xs) then
      search (SUM, cons (x, xs), n+1, sum+x)
    else search2 (SUM, xs, x+1, n, sum)
  ) else (
    case+ xs of
    | cons (x, xs) => search2 (SUM, xs, x+1, n-1, sum-x) | nil () => ~1
  ) // end of [if]
end // end of [search2]

(* ****** ****** *)

implement
main () = () where {
//
// 13 + 5197 + 5701 + 6733 + 8389 = 26033
//
  val ans = search (1 << 15, nil, 0, 0)
  val () = assert_errmsg (ans = 26033, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [problem60-hwxi.dats] *)
