//
// ProjectEuler: Problem 75
// Find the number of n's such that n can be expressed
// as the sum of a, b and c for exactly one set of a, b
// and c satisfying a^2+b^2=c^2
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

staload "libc/SATS/math.sats"

(* ****** ****** *)
//
// HX: note that a, b, c can be expressed as
// k*a1, k*b1, k*c1 for some a1, b1, c1 such
// that
//
// a1 = p^2-q^2
// b1 = 2*p*q
// c1 = p^2+q^2
//
// for some p and q satisfying gcd (p, q) = 1
//
// if a+b+c = a'+b'+c' and c=c' then
// 1) a=a' and b=b'
// 2) a=b' and b=a'
//
(* ****** ****** *)


#define N 1500000
val N1 = size1_of_int1 (N+1)
val theTable = array_make_elt<int> (N1, 0)
val theTable2 = array_make_elt<int> (N1, 0)

(* ****** ****** *)

val N2 = N / 2
val N2sqrt = int_of (sqrt (N2+0.5))

(* ****** ****** *)

fun theTable_init
  (): void = loop1 (2) where {
//
  fun loop2_set (c0: int, x0: Nat, c: int, x: Nat): void =
    if x <= N then let
      val t = theTable[x]
      val () = case+ t of
        | 0 => (theTable[x] := 1; theTable2[x] := c)
        | 1 => if theTable2[x] <> c then theTable[x] := 2
        | _ => ()
      // end of [val]
    in
      loop2_set (c0, x0, c+c0, x+x0)
    end else () // end of [if]
//
  fn* loop1 (p: int): void =
    if p < N2sqrt then loop2 (p, 1) else ()
  // end of [loop1]
  and loop2 (p: int, q: int): void =
    if q < p then let
      val () = if
        gcd (p, q) = 1 then let
        val p2 = p*p and pq = p*q and q2 = q*q
        val x = 2 * (p2 + pq)
        val x = uint_of (x)
        val x = uint1_of_uint (x)
        val x = int1_of_uint1 (x)
        val c = p2 + q2
        val () = loop2_set (c, x, c, x)
      in
        // nothing
      end // end of [if]
    in
      loop2 (p, q+1)
    end else loop1 (p+1)
  // end of [loop2]
} // end of [theTable_init]

(* ****** ****** *)

implement
main () = () where {
  val () = theTable_init ()
  var cnt: int = 0
  var i: natLte (N+1)
  val () = for
    (i := 1; i <= N; i := i+1)
    if theTable[i] = 1 then cnt := cnt + 1
  // end of [val]
  val ans = cnt
  val () = assert_errmsg (ans = 161667, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem75-hwxi.dats] *)
