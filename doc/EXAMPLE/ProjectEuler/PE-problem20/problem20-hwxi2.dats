//
// ProjectEuler: Problem 20
// Finding the sum of all the digits of 100!
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX-2010-09-19: this is a fully verified solution!
//
(* ****** ****** *)

datasort intlst =
  | intlst_cons of (int, intlst) | intlst_nil of ()
// end of [intlst]

(* ****** ****** *)

datatype intlst (intlst) =
  | {d:int} {ds:intlst}
    intlst_cons (intlst_cons (d, ds)) of (int d, intlst ds)
  | intlst_nil (intlst_nil) of ()
// end of [intlst]

macdef intlst_sing (x) = intlst_cons (,(x), intlst_nil)

(* ****** ****** *)

#define BASE 10
dataprop REP (intlst, int) =
  | {d:nat | d < BASE} {ds:intlst} {n:int}
    REPcons (intlst_cons (d, ds), BASE*n + d) of REP (ds, n)
  | REPnil (intlst_nil, 0) of ()
// end of [REP]

(* ****** ****** *)

fun int2intlst {n:nat} .<n>.
  (n: int n):<> [ds:intlst] (REP (ds, n) | intlst ds) =
  if n > 0 then let
    val n1 = n idiv BASE
    val d = n - BASE * n1
    val (pf | ds) = int2intlst (n1)
  in
    (REPcons pf | intlst_cons (d, ds))
  end else (REPnil | intlst_nil)
// end of [int2intlst]

fun cadd_intlst
  {c:nat} {ds:intlst} {n:int} .<ds>.
  (pf: REP (ds, n) | c: int c, ds: intlst ds)
  :<> [ds:intlst] (REP (ds, c+n) | intlst ds) =
  case+ ds of
  | intlst_cons (d, ds) => let
      prval REPcons (pf) = pf
      val d = d + c
      val c = d idiv BASE
      val d = d - BASE * c
      val (pf | ds) = cadd_intlst (pf | c, ds) in (REPcons pf | intlst_cons (d, ds))
    end // end of [intlst_cons]
  | intlst_nil () => let
      prval REPnil () = pf in int2intlst (c)
    end // end of [intlst_nil]
// end of [cadd_intlst]

(* ****** ****** *)

prfun lemma1 {k:int} .<>.
  {m,n:int} {p:int} (pf: MUL (m, n, p)): MUL (m, k*n, k*p) = let
//
  prval pf_kn = mul_make {k,n} ()
  prval pf_kn_m = mul_make {k*n,m} ()
  prval pf_nm = mul_commute (pf) // n*m=p
  prval pf_k_nm = mul_make {k,p} ()
//
  prval () = mul_is_associative (pf_kn, pf_nm, pf_kn_m, pf_k_nm) // kn*m=k*p
//
in
  mul_commute (pf_kn_m)
end // end of [lemma1]

(* ****** ****** *)

fun cmul_intlst
  {c:nat} {ds:intlst} {n:int} .<ds>.
  (pf: REP (ds, n) | c: int c, ds: intlst (ds))
  :<> [p:int;ds:intlst] (MUL (c, n, p), REP (ds, p) | intlst (ds)) =
  case+ ds of
  | intlst_cons (d, ds) => let
      prval REPcons pf = pf // n = BASE*n1 + d
      val (pfcd | cd) = c imul2 d
      prval () = mul_nat_nat_nat (pfcd)
      val c0 = cd idiv BASE
      val d1 = cd - BASE * c0 // cd = BASE * c0 + d
      val (pfmul, pfrep | ds) = cmul_intlst (pf | c, ds)
      val (pfrep | ds) = cadd_intlst (pfrep | c0, ds)
      prval pfmul = lemma1 {BASE} (pfmul)
      prval pfmul = mul_distribute (pfcd, pfmul)
    in
      (pfmul, REPcons (pfrep) | intlst_cons (d1, ds))
    end // end of [intlst_cons]
  | intlst_nil () => let
      prval REPnil () = pf
      prval pfmul = mul_make {c,0} ()
    in
      (pfmul, REPnil | intlst_nil)
    end // end of [intlst_nil]
// end of [cmul_intlst]

(* ****** ****** *)

dataprop SUM (intlst, int) =
  | {d:int} {ds:intlst} {t:int}
    SUMcons (intlst_cons (d, ds), d+t) of SUM (ds, t)
  | SUMnil (intlst_nil, 0)
// end of [SUM]

fun sum {ds:intlst} .<ds>.
  (ds: intlst (ds)):<> [t:int] (SUM (ds, t) | int (t)) =
  case+ ds of
  | intlst_cons (d, ds1) => let
      val (pf1 | t1) = sum (ds1) in (SUMcons (pf1) | d + t1)
    end
  | intlst_nil () => (SUMnil () | 0)
// end of [sum]

(* ****** ****** *)

dataprop FACT (int, int) =
  | FACTbas (0, 1)
  | {n:nat} {r,r1:int} FACTind (n+1, r1) of (FACT (n, r), MUL (n+1, r, r1))
// end of [FACT]

(* ****** ****** *)

fun fact {n:nat} .<n>. (n: int n)
  :<> [r:int;ds:intlst] (FACT (n, r), REP (ds, r) | intlst ds) =
  if n > 0 then let
    val (pffac, pfrep | ds) = fact (n-1)
    val (pfmul, pfrep | ds) = cmul_intlst (pfrep | n, ds)
  in
    (FACTind (pffac, pfmul), pfrep | ds)
  end else
    (FACTbas (), REPcons (REPnil ()) | intlst_sing (1))
  // end of [if]
(* end of [fact] *)

(* ****** ****** *)

fun p20 {n:nat} .<>. (n: int n)
  :<> [t:int;r:int;ds:intlst] (FACT (n, r), REP (ds, r), SUM (ds, t) | int t) = let
  val (pffac, pfrep | ds) = fact (n); val (pfsum | t) = sum (ds)
in
  (pffac, pfrep, pfsum | t)
end // end of [p20]

(* ****** ****** *)

implement main () = () where {
//
  val (_, _, _ | ans) = p20 (100)
  val () = assert_errmsg (ans = 648, #LOCATION)
  val () = (print "the sum of all the digits of 100! is "; print ans; print_newline ())
//
} // end of [main]

(* ****** ****** *)

(* end of [problem20-hwxi2.dats] *)
