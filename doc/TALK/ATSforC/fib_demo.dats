(* ****** ****** *)
//
// HX: this is tail-recursive implementation of fib
//
(* ****** ****** *)

dataprop FIB (int, int) =
  | FIB0 (0, 0) of () // fib(0) = 0
  | FIB1 (1, 1) of () // fib(1) = 1
  | {n:nat}{r0,r1:nat} // fib(n+2) = fib(n)+fib(n+1)
    FIB2 (n+2, r0+r1) of (FIB (n, r0), FIB (n+1, r1))
// end of [FIB]

(* ****** ****** *)

extern
fun fib {n:nat}
  (n: int (n)): [r:nat] (FIB (n, r) | int (r))
// end of [fib]

(* ****** ****** *)

implement
fib {n} (n) = let
  fun loop
    {i:nat | i < n} {r0,r1:nat} (
    pf0: FIB (i, r0), pf1: FIB (i+1, r1)
  | ni: int (n-i), r0: int r0, r1: int r1
  ) : [r:nat] (FIB (n, r) | int r) =
    if ni > 1 then
      loop {i+1} (pf1, FIB2 (pf0, pf1) | ni-1, r1, r0+r1)
    else (pf1 | r1)
  // end of [loop]
in
  case+ n of
  | 0 => (FIB0 () | 0)
  | 1 => (FIB1 () | 1)
  | _ =>> loop {0} (FIB0, FIB1 | n, 0, 1)
end // end of [fib]

(* ****** ****** *)

implement
main () = let
//
#define N 10
#define LN 40
//
fun loop (
  i: natLte (N)
) : void =
  if i < N then let
    val (pf | ans) = fib (i)
    val () = printf ("fib(%i) = %i\n", @(i, ans))
  in
    loop (i+1)
  end else () // end of [if]
//
val () = loop (0)
//
val (pf | ans) = fib (LN)
val () = printf ("fib(%i) = %i\n", @(LN, ans))
//
in
end // end of [main]

(* ****** ****** *)

(* end of [fib_tailrec.dats] *)
