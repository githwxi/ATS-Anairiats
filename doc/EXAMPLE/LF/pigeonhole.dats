(*
**
** A proof of the pigeonhole principle in ATS
**
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: September 28, 2009
**
*)

(*

What is encoded and proven in ATS is the following formulation of
pigeonhole principle:

Let P be a relation on pairs of integers and m and n be two naturnal
numbers satisfying m > n and n >= 1. If there exists a natural number
j < n for each given naturnal number i < m such that P (i, j) holds,
then there exists i1, i2 and j satisfying 0 <= i1 < i2 < m and j < n
such that both P (i1, j) and P (i2, j) hold.

*)

sortdef
int2rel = (int, int) -> prop // for binary relations on integers

prfun pigeonhole
  {P: int2rel} {m,n:nat | m > n; n >= 1} .<m>. (
    fpf: {i:nat | i < m} () -> [j:nat | j < n] P (i, j)
  ) : [i1,i2,j:nat | i1 < i2; i2 < m] (P (i1, j), P (i2, j)) = sif n >= 2 then let
  val [x:int] pf0 = fpf {m-1} ()
  dataprop P1 (i:int, int) =
    | P1r1 (i, 0) of P (i, x)
    | {x>0} P1r2 (i, x-1) of P (i, 0)
    | {j:int | j > 0; j <> x} P1r3 (i, j-1) of P (i, j)
  prfn fpf1 {i:nat | i < m-1} (): [j:nat | j < n-1] P1 (i, j) = let
    val [j:int] pf = fpf {i} ()
  in
    sif j == 0 then
      (sif x == 0 then P1r1 (pf) else P1r2 (pf))
    else
      (sif j == x then P1r1 (pf) else P1r3 (pf))
    // end of [sif]
  end // end of [fpf1]
  val (pf1, pf2) = pigeonhole {P1} {m-1,n-1} (fpf1)
in
  case+ pf1 of
  | P1r1 (pf1) => (pf1, pf0)
  | P1r2 (pf1) => begin case+ pf2 of
    | P1r1 pf2 => (pf2, pf0) | P1r2 pf2 => (pf1, pf2)
    end // end of [P1r2]
  | P1r3 (pf1) => begin case+ pf2 of
    | P1r1 pf2 => (pf2, pf0) | P1r3 pf2 => (pf1, pf2)
    end // end of [P1r3]
end else begin // n = 1
  (fpf {0} (), fpf {1} ())
end // end of [pigenhole]

(* ****** ****** *)

(* end of [pigeonhole.dats] *)
