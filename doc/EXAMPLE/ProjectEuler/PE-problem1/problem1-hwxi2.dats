//
// ProjectEuler: Problem 1
// Finding the sum of all numbers below 1000 that is a multiple of 3 or 5
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//
(* ****** ****** *)
//
// HX-2010-08: this is a fully verified solution!
//
(* ****** ****** *)

absprop MOD (n:int, p:int, r:int) // n mod p = r

nonfix mod
extern fun mod {n:nat} {p:pos}
  (n: int n, p: int p): [r:nat] (MOD (n, p, r) | int r)
  = "atspre_mod_int_int"
// end of [mod]

(* ****** ****** *)
//
// SUM35 (n, t) = sum of i <= n such that i mod 3 = 0 or i mod 5 = 0
//
dataprop SUM35 (int(*n*), int(*t*)) =
  | SUM35bas (0, 0)
  | {n:pos} {s1:nat} SUM35ind1 (n, s1+n) of (SUM35 (n-1, s1), MOD (n, 3, 0))
  | {n:pos} {s1:nat} SUM35ind2 (n, s1+n) of (SUM35 (n-1, s1), MOD (n, 5, 0))
  | {n:pos} {s1:nat} {r3,r5:pos}
      SUM35ind3 (n, s1) of (SUM35 (n-1, s1), MOD (n, 3, r3), MOD (n, 5, r5))
// end of [SUM35]

(* ****** ****** *)

extern fun sum35 {n:nat} (n: int n): [t:nat] (SUM35 (n, t) | int t)

implement sum35 (n) = let
  fun loop {n:nat} {t0:int} .<n>.
    (n: int n, t0: int t0): [t:int | t >= t0] (SUM35 (n, t-t0) | int (t)) =
    if n > 0 then let
      val (pf3 | r3) = mod (n, 3)
    in
      if r3 = 0 then let
        val (pf | t) = loop (n-1, t0+n) in (SUM35ind1 (pf, pf3) | t)
      end else let
        val (pf5 | r5) = mod (n, 5)
      in
        if r5 = 0 then let
          val (pf | t) = loop (n-1, t0+n) in (SUM35ind2 (pf, pf5) | t)
        end else let
          val (pf | t) = loop (n-1, t0) in (SUM35ind3 (pf, pf3, pf5) | t)
        end // end of [if]
      end // end of [if]
    end else (SUM35bas () | t0)
  // end of [loop]
in
  loop (n, 0)
end // end if [sum35]

(* ****** ****** *)

implement main () = () where {
(*
  val N = 10
  val (_pf | ans) = sum35 (N-1)
  val () = (
    printf ("The sum of all the natural numbers < %i that are multiples of 3 or 5 = ", @(N));
    print ans;
    print_newline ()
  ) // end of [val]
*)
  val N = 1000
  val (_pf | ans) = sum35 (N-1)
  val () = assert_errmsg (ans = 233168, #LOCATION)
  val () = (
    printf ("The sum of all the natural numbers < %i that are multiples of 3 or 5 = ", @(N));
    print ans;
    print_newline ()
  ) // end of [val]
} // end of [main]

(* ****** ****** *)

(* end of [problem1-hwxi2.dats] *)
