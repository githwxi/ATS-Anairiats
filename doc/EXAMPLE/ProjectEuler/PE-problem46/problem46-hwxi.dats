//
// ProjectEuler: Problem 46
// Finding the largest pandigital prime
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"

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

fun test
  {k:nat} (k: int k): bool = let
  val k2 = isqrt ((uint_of)k)
  val k2 = (int_of)k2
  var i: intGte 1 // unitialized
  var res: bool = false
  val () = for
    (i := 1; i <= k2; i := i+1)
    if isprime (2*k+1-2*i*i) then (res := true; break)
  // end of [val]
in
  res
end // end of [test]

fun search
  {k:nat} (k: int k): int =
  if isprime (2*k+1) then search (k+1) else (if test (k) then search (k+1) else k)
// end of [search]

(* ****** ****** *)

implement
main () = () where {
  val k = search (1)
  val ans = 2*k + 1
  val () = assert_errmsg (ans = 5777, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem46-hwxi.dats] *)
