//
// ProjectEuler: Problem 6
// Finding the difference (1+...+n)^2 - (1^2+...+n^2)
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010 // the current fully verified solution
//
(* ****** ****** *)
//
// HX-2010-09: this is a fully verified solution!
//
(* ****** ****** *)

dataprop SUM1 (int, int) =
  | SUM1bas (0, 0) of ()
  | {n:nat} {s:int} SUM1ind (n+1, s+n+1) of SUM1 (n, s)
// end of [SUM1]

dataprop SUM2 (int, int) =
  | SUM2bas (0, 0) of ()
  | {n:nat} {s,p:int} SUM2ind (n+1, s+p) of (SUM2 (n, s), MUL (n+1, n+1, p))
// end of [SUM2]

//
// HX: this is a specification for the problem
//
propdef P6 (n:int, d:int) =
  [s1,s2,p:int | p-s2==d] (SUM1 (n, s1), SUM2 (n, s2), MUL (s1, s1, p))
// end of [P6]

(* ****** ****** *)

prfun SUM1istot
  {n:nat} .<n>. (): [r:int] SUM1 (n, r) =
  sif n > 0 then SUM1ind (SUM1istot {n-1} ()) else SUM1bas ()
// end of [SUM1istot]

prfun lemma1 {n:nat} {s,p:int} .<n>.
  (pf1: SUM1 (n, s), pf2: MUL (n, n+1, p)): [2*s == p] void =
  sif n == 0 then let
    prval SUM1bas () = pf1 and MULbas () = pf2
  in
    // nothing
  end else let // n > 0
    prval SUM1ind (pf1) = pf1 // pf1: SUM1 (n-1, s-n)
    prval pf2 = mul_commute (pf2) // pf2: MUL (n+1, n, p)
    prval MULind (pf2) = pf2 // pf2: MUL (n, n, p-n)
    prval MULind (pf2) = pf2 // pf2: MUL (n-1, n, p-n-n)
    prval () = lemma1 (pf1, pf2) // [2*(s-n) == (p-n-n)]
  in
    // nothing
  end // end of [sif]
// end of [lemma1]

fun sum1 {n:nat} .<>.
  (n: int n):<> [s:int] (SUM1 (n, s) | int s) = let
  prval pf1 = SUM1istot ()
  val (pf2 | p) = n imul2 (n+1)
  prval () = lemma1 (pf1, pf2)
in
  (pf1 | p / 2)
end // end of [sum1]

(* ****** ****** *)

prfun SUM2istot
  {n:nat} .<n>. (): [r:int] SUM2 (n, r) =
  sif n > 0 then SUM2ind (SUM2istot {n-1} (), mul_istot {n,n} ()) else SUM2bas ()
// end of [SUM2istot]

//
// HX: please don't ask me what is going on here :)
//
prfun lemma2 {n:nat} {s,p1,p2:int} .<n>.
  (pf1: SUM2 (n, s), pf21: MUL (n, n+1, p1), pf22: MUL (p1, 2*n+1, p2)): [6*s == p2] void =
  sif n == 0 then let
    prval SUM2bas () = pf1
    prval MULbas () = pf21; prval MULbas () = pf22
  in
    // nothing
  end else let // n > 0
//
    prval SUM2ind (pf1, pfnn) = pf1 // pf1: SUM2 (n-1, s-nn)
//
    prval pf21_ = mul_expand_linear {1,0} {1,1} (pfnn) // p1 = nn + n
    prval () = mul_isfun (pf21, pf21_)
//
    prval pf21 = mul_commute (pf21) // pf21: MUL (n+1, n, p1)
    prval MULind (pf21) = pf21 // pf21: MUL (n, n, p1-n)
    prval MULind (pf21) = pf21 // pf21: MUL (n-1, n, p1-n-n)
//
    prval pf22 = mul_commute (pf22) // pf22: MUL (2n+1, p1, p2)
    prval MULind (pf22) = pf22 // pf22: MUL (2n, p1, p2-p1)
    prval pf3 = mul_expand_linear {2,0}{~2,0} (pfnn) // 2n*(-2n)=-4nn
    prval pf22 = mul_distribute (pf22, pf3) // pf22: MUL (2n, p1-2n, p2-p1-4nn)
    prval MULind (pf22) = pf22 // pf22: MUL (2n-1, p1-2n, p2-p1-4nn-p1+2n)
    prval pf22 = mul_commute (pf22) // pf22: MUL (p1-2n, 2n-1, p2-p1-4nn-p1+2n)
//
    prval () = lemma2 {n-1} (pf1, pf21, pf22)
//
  in
    // nothing
  end // end of [sif]
// end of [lemma2]

fun sum2 {n:nat} .<>.
  (n: int n):<> [s:int] (SUM2 (n, s) | int s) = let
  prval pf1 = SUM2istot ()
  val (pf21 | p1) = n imul2 (n+1)
  val (pf22 | p2) = p1 imul2 (2*n+1)
  prval () = lemma2 (pf1, pf21, pf22)
in
  (pf1 | p2 / 6)
end // end of [sum2]

(* ****** ****** *)

extern
fun p6 {n:nat} (n: int n):<> [d:int] (P6 (n, d) | int d)

implement p6 (n) = let
  val (pf1 | s1) = sum1 (n)
  val (pf2 | s2) = sum2 (n)
  val (pf3 | p) = s1 imul2 s1
  prval pf = (pf1, pf2, pf3)
in
  (pf | p-s2)
end // end of [p6]

(* ****** ****** *)

implement main () = () where {
  #define N 100
//
  val (_pf | ans) = p6 (N)
//
  val () = (print "ans = "; print ans; print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [problem6-hwxi.dats] *)
