//
// ProjectEuler: Problem 37
// Finding the sum of all 11 trunctable primes
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)
//
// for a truncatable prime containing at least 4 digits, it must be of the form:
// ?XY...YX?
// where ? is 3 or empty and X is either 1 or 7 and Y is either 3 or 9
//
(* ****** ****** *)

staload "prelude/DATS/list_vt.dats"

(* ****** ****** *)

fun isqrt
  (x: uint): uint =
  if x >= 2U then let
    val x4 = x / 4U
    val r2 = isqrt (x4)
    val r = r2 + r2
    val r_1 = r + 1U
  in
    if r_1 * r_1 > x then r else r_1
  end else x 
// end of [isqrt]

(* ****** ****** *)

fn isprime
  {n:nat | n >= 2}
  (n: int n): bool = let
  val u = uint_of_int (n)
  val r = isqrt (u)
(*
  val () = (print "u = "; print u; print_newline ())
  val () = (print "r = "; print r; print_newline ())
*)
  fun loop (p: uint):<cloref1> bool =
    if p <= r then
      (if (u mod p > 0U) then loop (p+1U) else false)
    else true
  // end of [loop]
in
  loop (2U)
end // end of [isprime]

fn isprime
  (n: int): bool = let
  val n = int1_of_int (n)
in
  if n >= 2 then isprime n else false
end // end of [isprime]

(* ****** ****** *)

fun toDigits
  (n: int): List_vt (int) = let
  fun loop (n: int, res: List_vt (int)): List_vt (int) =
    if n > 0 then let
      val r = n mod 10 in loop (n/10, list_vt_cons (r, res))
    end else res
in
  loop (n, list_vt_nil)
end // end of [toDigits]

(* ****** ****** *)

fun testDigits1 {n:nat}
  (ds: !list_vt (int, n)): bool = let
  fun loop {n:nat} (ds: !list_vt (int, n), i: int): bool =
    case+ ds of
    | list_vt_cons (d, !p_ds1) => let
        val i = 10 * i + d
      in
       if isprime (i) then let
         val res = loop (!p_ds1, i) in (fold@ ds; res)
       end else (fold@ ds; false)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ ds; true)
  // end of [loop]
in
  loop (ds, 0)
end // end of [testDigits1]

fun testDigits2 {n:nat}
  (ds: !list_vt (int, n)): bool = let
  fun loop {n:nat} (ds: !list_vt (int, n), c: int, i: int): bool =
    case+ ds of
    | list_vt_cons (d, !p_ds1) => let
        val i = c * d + i
      in
       if isprime (i) then let
         val res = loop (!p_ds1, 10*c, i) in (fold@ ds; res)
       end else (fold@ ds; false)
      end // end of [list_vt_cons]
    | list_vt_nil () => (fold@ ds; true)
  // end of [loop]
in
  loop (ds, 1, 0)
end // end of [testDigits2]

(* ****** ****** *)

fun eval1 {n:nat} .<n>.
  (ds: !list_vt (int, n), res: int): int =
  case+ ds of
  | list_vt_cons (d, !p_ds1) => let
      val res = eval1 (!p_ds1, 10*res + d) in fold@ (ds); res
    end // end of [list_vt_cons]
  | list_vt_nil () => (fold@ ds; res)
// end of [eval1]

fun eval2 {n:nat} .<n>.
  (ds: !list_vt (int, n), c: int, res: int): int =
  case+ ds of
  | list_vt_cons (d, !p_ds1) => let
      val res = eval2 (!p_ds1, 10*c, c*d+res) in fold@ (ds); res
    end // end of [list_vt_cons]
  | list_vt_nil () => (fold@ ds; res)
// end of [eval2]

(* ****** ****** *)

fun test
  (n:int): int = let
  val ds = toDigits (n)
(*
  val x = eval1 (ds, 0)
  val () = (print "test: x = "; print x; print_newline ())
*)
in
  if testDigits1 (ds) then let
    val ds = list_vt_reverse (ds)
    val test = testDigits2 (ds)
    val x1 = if test then eval2 (ds, 1, 0) else 0
    val () = list_vt_free (ds)
  in
    x1
  end else let
    val () = list_vt_free (ds) in 0
  end // end of [if]
end // end of [test]

(* ****** ****** *)

fun pow (x: int, n: int): int =
  if n > 0 then x * pow (x, n-1) else 1

(* ****** ****** *)

implement
main () = () where {
  val N = pow (10, 6) - 1
(*
  val () = (print "N = "; print N; print_newline ())
*)
  var i: int = 10
  var cnt: int = 0
  var sum: int = 0
  val () = while (true) let
    val x = test(i)
    val () = if x > 0 then let
      val () = cnt := cnt + 1
      val () = sum := sum + x
      val () = (print "x = "; print x; print_newline ())
    in
      // nothing
    end // end of [if]
    val () = if cnt = 11 then break // HX: this is like cheating :)
  in
    i := i + 1
  end // end of [while]
  val ans = sum
  val () = assert_errmsg (ans = 748317, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem37-hwxi.dats] *)
