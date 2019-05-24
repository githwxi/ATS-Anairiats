(* ****** ****** *)
//
// HX: some code used in the slides
//
(* ****** ****** *)

datatype FIB (int, int) =
  | FIB0 (0, 0) of () // fib(0) = 0
  | FIB1 (1, 1) of () // fib(1) = 1
  | {n:nat}{r0,r1:int} // fib(n+2) = fib(n)+fib(n+1)
    FIB2 (n+2, r0+r1) of (FIB (n, r0), FIB (n+1, r1))

(* ****** ****** *)

fun fib {n:nat}
  (n: int (n)): [r:nat] (FIB (n, r) | int (r)) =
  case+ n of
  | 0 => (FIB0 () |  0)
  | 1 => (FIB1 () |  1)
  | _ =>> let
      val (pf0 | r0) = fib (n-2)
      val (pf1 | r1) = fib (n-1)
    in
      (FIB2 (pf0, pf1) | r0 + r1)
    end // end of [_]
// end of [fib]

(* ****** ****** *)

fun fibats (n: int): int = let
  fun loop (r0: int, r1: int, ni: int): int =
    if ni > 0 then loop (r1, r0+r1, ni-1) else r0
  // end of [loop]
in
  loop (0, 1, n)
end // end of [fibats]

(* ****** ****** *)

fun fibats2 {n:nat} (n: int n)
  : [r:int] (FIB (n, r) | int r) = let
  fun loop {n,i:nat | i <= n} {r0,r1:int} .<n-i>.
  (
    pf0: FIB (i, r0)
  , pf1: FIB (i+1, r1)
  | r0: int (r0), r1: int (r1), ni: int(n-i)
  ) : [r:int] (FIB (n, r) | int (r)) =
    if ni > 0 then
      loop {n,i+1} (pf1, FIB2 (pf0, pf1) | r1, r0+r1, ni-1)
    else (pf0 | r0) // end of [if]
in
  loop (FIB0(), FIB1() | 0, 1, n)
end // end of [fibats2]

(* ****** ****** *)

implement
main () =
{
val N = 10
val res = fibats (10)
val () = println! ("res = ", res)
val pfres = fibats2 (10)
val () = println! ("pfres.1 = ", pfres.1)
val () = assertloc (res = pfres.1)
} // end of [main]

(* ****** ****** *)

(* end of [fib.dats] *)
