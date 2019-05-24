//
// ProjectEuler: Problem 51
// Finding the smallest number that can form 8 primes by changing the
// same part of its digits
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX-2010-09-20: A really ugly problem of _no_ value that I can see!!!
//
(* ****** ****** *)

staload "prelude/DATS/array.dats"
staload "prelude/DATS/reference.dats"

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

#define BASE 10

fun DA_get {n:nat}
  (DA: &(@[int][n]), n: size_t n): int = let
  val _0 = (size1_of_int1)0
  var res: int = 0
  var i: sizeLte n // unintialized
  val () = for
    (i := _0; i < n; i := i + 1) res := res * BASE + DA[i]
  // end of [val]
in
  res
end // end of [DA_get]

fun DA_set {n:nat}
  (DA: &(@[int][n]), n: size_t n, x: int): void = let
  val _0 = (size1_of_int1)0
  var x: int = x
  var i: sizeLte n // unintialized
  val () = for (
    i := _0; i < n; i := i + 1
  ) let
    val ind = n-1-i in
    if DA.[ind] >= 0 then (DA.[ind] := (x mod BASE); x := x / BASE)
  end  // end of [val]
in
  // nothing
end // end of [DA_set]

(* ****** ****** *)

val theAnswer = ref<int> (0)

(* ****** ****** *)

fun eval3 {n:int} {i,j,k:int | 0 <= i; i < j; j < k; k < n} (
    DA: &(@[int][n]), n: size_t n, i: int i, j: int j, k: int k, d: int, res: int
  ) : int =
  if i = 0 andalso d = 0 then 
    eval3 (DA, n, i, j, k, d+1, res)
  else if d < BASE then let
    val () = DA[i] := d
    val () = DA[j] := d
    val () = DA[k] := d
    val x = DA_get (DA, n)
(*
    val () = (print "eval3: x = "; print x; print_newline ())
*)
  in
    if isprime (x) then let
      val () = if (res = 0) then !theAnswer := x
    in
      eval3 (DA, n, i, j, k, d+1, res+1)
    end else
      eval3 (DA, n, i, j, k, d+1, res)
    // end of [if]
  end else res
// end of [eval3]

(* ****** ****** *)

#define NPRIME 8

fn* search1 {n:int} {i:nat | i <= n} (
    x0: int, DA: &(@[int][n]), n: size_t n, i: int i
  ) : bool =
  if i < n then search2 (x0, DA, n, i, i+1) else false

and search2 {n:int}
  {i,j:int | 0 <= i; i < j; j <= n} (
    x0: int, DA: &(@[int][n]), n: size_t n, i: int i, j: int j
  ) : bool =
  if j < n then search3 (x0, DA, n, i, j, j+1) else search1 (x0, DA, n, i+1)

and search3 {n:int}
  {i,j,k:int | 0 <= i; i < j; j < k; k <= n} (
    x0: int, DA: &(@[int][n]), n: size_t n, i: int i, j: int j, k: int k
  ) : bool =
  if k < n then let
    val () = DA[i] := ~1
    val () = DA[j] := ~1
    val () = DA[k] := ~1
    val () = DA_set (DA, n, x0)
    val res = eval3 (DA, n, i, j, k, 0(*d*), 0(*res*))
  in
    if res < NPRIME then
      search3 (x0, DA, n, i, j, k+1)
    else true // end of [if]
  end else
    search2 (x0, DA, n, i, j+1)
  // end of [if]
// end of [search3]

(* ****** ****** *)

fun log10 (x: int): Nat =
  if x > 0 then 1 + log10 (x/10) else 0
// end of [log10]

fun test
  (x: int): bool = let
  val nd = log10 (x) + 3 // plus 3 more digits
  val nd = size1_of_int1(nd)
  var !p_DA = @[int][nd](0)
  val () = DA_set (!p_DA, nd, x)
in
  search1 (x, !p_DA, nd, 0)
end // end of [test]

(* ****** ****** *)

implement
main () = () where {
  var x0: int = 0
  val () = while (true) let
(*
    val () = (print "x0 = "; print x0; print_newline ())
*)
    val () = if test (x0) then break
  in
    x0 := x0 + 1
  end // end of [val]
  val ans = !theAnswer
  val () = assert_errmsg (ans = 121313, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem51-hwxi.dats] *)
