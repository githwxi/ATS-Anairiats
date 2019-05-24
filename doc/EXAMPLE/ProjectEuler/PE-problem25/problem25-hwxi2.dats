//
// ProjectEuler: Problem 25
// Finding the first Fibonacci term containing at least 1000 digits
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX-2010-09-19: this is a fully verified solution
//
(* ****** ****** *)

datasort intlst =
  | intlst_cons of (int, intlst) | intlst_nil of ()
// end of [intlst]

(* ****** ****** *)

datatype intlst (intlst) =
  | {d:nat} {ds:intlst}
    intlst_cons (intlst_cons (d, ds)) of (int d, intlst ds)
  | intlst_nil (intlst_nil) of ()
// end of [intlst]

macdef intlst_sing (x) = intlst_cons (,(x), intlst_nil)

(* ****** ****** *)

dataprop LENGTH (intlst, int) =
  | LENGTHnil (intlst_nil, 0)
  | {d:int} {ds:intlst} {n:nat}
    LENGTHcons (intlst_cons (d, ds), n+1) of LENGTH (ds, n)
// end of [LENGTH]

fun length {ds:intlst} .<ds>.
  (ds: intlst ds):<> [n:nat] (LENGTH (ds, n) | int n) =
  case+ ds of
  | intlst_cons (_, ds) => let
      val (pf | n) = length (ds) in (LENGTHcons pf | n+1)
    end // end of [intlst_cons]
  | intlst_nil () => (LENGTHnil | 0)
// end of [length]

(* ****** ****** *)

#define BASE 10
dataprop REP1 (intlst, int) =
  | {d:nat | d < BASE} {ds:intlst} {n:nat}
    REP1cons (intlst_cons (d, ds), BASE*n + d) of REP1 (ds, n)
  | {d:pos | d < BASE} REP1sing (intlst_cons (d, intlst_nil), d) of ()
  | REP1nil (intlst_nil, 0) of ()
// end of [REP1]

prfun rep1_cons0
  {ds:intlst} {n:pos} .<>.
  (pf: REP1 (ds, n)): REP1 (intlst_cons (0, ds), BASE*n) =
  case+ pf of
  | REP1nil () =/=> () | _ =>> REP1cons (pf)
// end of [rep1_cons0]

prfun rep1_cons1
  {d:pos | d < BASE} {ds:intlst} {n:nat} .<>.
  (pf: REP1 (ds, n)): REP1 (intlst_cons (d, ds), BASE*n+d) =
  case+ pf of
  | REP1nil () => REP1sing () | _ =>> REP1cons (pf)
// end of [rep1_cons]

prfun rep1_uncons
  {d:int} {ds:intlst} {n:int} .<>.
  (pf: REP1 (intlst_cons (d, ds), n)): [n1:nat | d < BASE; n==BASE*n1+d] REP1 (ds, n1) =
  case+ pf of
  | REP1cons (pf) => pf
  | REP1sing () => REP1nil
// end of [rep1_uncons]

(* ****** ****** *)

dataprop FIB (int, int) =
  | FIBbas0 (0, 0)
  | FIBbas1 (1, 1)
  | {n:nat} {r0,r1:nat} FIBind (n+2, r0+r1) of (FIB (n, r0), FIB (n+1, r1))
// end of [FIB]

(* ****** ****** *)

#define NMAX 1000
dataprop NFOUND (int) =
  | NFOUNDbas (0)
  | {n:nat} {r:nat} {ds:intlst} {nd:nat | nd < NMAX}
    NFOUNDind (n+1) of (NFOUND (n), FIB (n, r), REP1 (ds, r), LENGTH (ds, nd))
// end of [NFOUND]

(* ****** ****** *)

extern
fun add_intlst_intlst {ds1,ds2:intlst} {n1,n2:nat}
  (pf1: REP1 (ds1, n1), pf2: REP1 (ds2, n2) | ds1: intlst (ds1), ds2: intlst (ds2)):<>
  [ds:intlst] (REP1 (ds, n1+n2) | intlst (ds)) = "add_intlst_intlst"

//
// HX-2010-09-18:
// this implementation is not tail-recursive but it is good enough to get the job done
//
implement add_intlst_intlst
  (pf1, pf2 | ds1, ds2) = aux2 (pf1, pf2 | 0, ds1, ds2) where {
  fun aux1 {ds:intlst} {n:nat} .<ds>.
    (pf: REP1 (ds, n) | ds: intlst ds):<> [ds:intlst] (REP1 (ds, n+1) | intlst ds) =
    case+ ds of
    | intlst_cons (d, ds) => let
        prval pf = rep1_uncons (pf); val d = d + 1
      in
        if d < BASE then
          (rep1_cons1 pf | intlst_cons (d, ds))
        else let
          val (pf | ds) = aux1 (pf | ds) in (rep1_cons0 pf | intlst_cons (0, ds))
        end (* end of [if] *)
      end // end of [intlst_cons]
    | intlst_nil () => let
        prval REP1nil () = pf in (REP1sing | intlst_sing (1))
      end // end of [intlst_nil]
  // end of [aux1]
  fun aux2 {c:two} {ds1,ds2:intlst} {n1,n2:nat} .<ds1>. (
      pf1: REP1 (ds1, n1), pf2: REP1 (ds2, n2) | c: int c, ds1: intlst ds1, ds2: intlst ds2
    ) :<> [ds:intlst] (REP1 (ds, n1+n2+c) | intlst (ds)) =
    case+ ds1 of
    | intlst_cons (d1, ds10) => let
        prval pf10 = rep1_uncons (pf1)
      in
        case+ ds2 of
        | intlst_cons (d2, ds20) => let
            prval pf20 = rep1_uncons (pf2)
            val d = d1 + d2 + c
          in
            if d < BASE then let
              val (pf | ds) = aux2 (pf10, pf20 | 0, ds10, ds20)
            in
              (REP1cons pf | intlst_cons (d, ds))
            end else let
              val (pf | ds) = aux2 (pf10, pf20 | 1, ds10, ds20)
            in
              (REP1cons pf | intlst_cons (d-BASE, ds))
            end (* end of [if] *)
          end // end of [intlst_cons]
        | intlst_nil () => let
            prval REP1nil () = pf2 in if c > 0 then aux1 (pf1 | ds1) else (pf1 | ds1)
          end // end of [intlst_nil]
      end // end of [intlst_cons]
    | intlst_nil () => let
        prval REP1nil () = pf1
      in
        if c > 0 then aux1 (pf2 | ds2) else (pf2 | ds2)
      end // end of [intlst_nil]
  // end of [aux2]
} // end of [add_intlst_intlst]

(* ****** ****** *)

fun search {n:nat}
  {r1,r2:nat} {ds1,ds2:intlst} (
  pf0: NFOUND n
, pf11: FIB (n, r1), pf12: REP1 (ds1, r1)
, pf21: FIB (n+1, r2), pf22: REP1 (ds2, r2)
| ds1: intlst ds1, ds2: intlst ds2, n: int n
) : [n:nat;r:nat;ds:intlst;nd:nat | nd >= NMAX] (
  NFOUND n, FIB (n, r), REP1 (ds, r), LENGTH (ds, nd) | int n
) = let
  val (pf1len | nd1) = length (ds1)
in
  if nd1 < NMAX then let
    prval pf31 = FIBind (pf11, pf21)
    val (pf32 | ds3) = add_intlst_intlst (pf12, pf22 | ds1, ds2)
  in
    search (NFOUNDind (pf0, pf11, pf12, pf1len), pf21, pf22, pf31, pf32 | ds2, ds3, n+1)
  end else let
(*
    val () = assert (nd1 = NMAX)
*)
  in
    (pf0, pf11, pf12, pf1len | n)
  end // end of [if]
end // end of [search]

(* ****** ****** *)

extern
fun p25 ()
  : [n:nat;r:nat;ds:intlst;nd:nat | nd >= NMAX] (
  NFOUND n, FIB (n, r), REP1 (ds, r), LENGTH (ds, nd) | int n
) // end of [p25]

implement p25 () = let
  prval pf0 = NFOUNDbas ()
  prval pf11 = FIBbas0 ()
  prval pf12 = REP1nil ()
  val ds1 = intlst_nil ()
  prval pf21 = FIBbas1 ()
  prval pf22 = REP1sing ()
  val ds2 = intlst_sing (1)
in
  search (pf0, pf11, pf12, pf21, pf22 | ds1, ds2, 0)
end // end of [p25]

(* ****** ****** *)

implement main () = () where {
//
  val (_, _, _, _ | ans) = p25 ()
//
  val () = assert_errmsg (ans = 4782, #LOCATION)
  val () = printf ("F(%i) is the first Fibonacci term containing at least 1000 digits.\n", @(ans))
//
} // end of [main]

(* ****** ****** *)

(* end of [problem25-hwxi2.dats] *)
