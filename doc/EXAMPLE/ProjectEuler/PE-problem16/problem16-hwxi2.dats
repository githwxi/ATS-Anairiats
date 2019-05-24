//
// ProjectEuler: Problem 16
// Finding the sum of all the digits of 2^1000
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// HX-2010-09-18: this is a fully verified solution!
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

extern
fun add_intlst_intlst {ds1,ds2:intlst} {n1,n2:int}
  (pf1: REP (ds1, n1), pf2: REP (ds2, n2) | ds1: intlst (ds1), ds2: intlst (ds2)):<>
  [ds:intlst] (REP (ds, n1+n2) | intlst (ds)) = "add_intlst_intlst"

//
// HX-2010-09-18:
// this implementation is not tail-recursive but it is good enough to get the job done
//
implement add_intlst_intlst
  (pf1, pf2 | ds1, ds2) = aux2 (pf1, pf2 | 0, ds1, ds2) where {
  fun aux1 {ds:intlst} {n:int} .<ds>.
    (pf: REP (ds, n) | ds: intlst ds):<> [ds:intlst] (REP (ds, n+1) | intlst ds) =
    case+ ds of
    | intlst_cons (d, ds) => let
        prval REPcons (pf) = pf; val d = d + 1
      in
        if d < BASE then
          (REPcons pf | intlst_cons (d, ds))
        else let
          val (pf | ds) = aux1 (pf | ds) in (REPcons pf | intlst_cons (0, ds))
        end (* end of [if] *)
      end // end of [intlst_cons]
    | intlst_nil () => let
        prval REPnil () = pf in (REPcons (REPnil) | intlst_sing (1))
      end // end of [intlst_nil]
  // end of [aux1]
  fun aux2 {c:two} {ds1,ds2:intlst} {n1,n2:int} .<ds1>. (
      pf1: REP (ds1, n1), pf2: REP (ds2, n2) | c: int c, ds1: intlst ds1, ds2: intlst ds2
    ) :<> [ds:intlst] (REP (ds, n1+n2+c) | intlst (ds)) =
    case+ ds1 of
    | intlst_cons (d1, ds10) => let
        prval REPcons pf10 = pf1
      in
        case+ ds2 of
        | intlst_cons (d2, ds20) => let
            prval REPcons pf20 = pf2
            val d = d1 + d2 + c
          in
            if d < BASE then let
              val (pf | ds) = aux2 (pf10, pf20 | 0, ds10, ds20)
            in
              (REPcons pf | intlst_cons (d, ds))
            end else let
              val (pf | ds) = aux2 (pf10, pf20 | 1, ds10, ds20)
            in
              (REPcons pf | intlst_cons (d-BASE, ds))
            end (* end of [if] *)
          end // end of [intlst_cons]
        | intlst_nil () => let
            prval REPnil () = pf2 in if c > 0 then aux1 (pf1 | ds1) else (pf1 | ds1)
          end // end of [intlst_nil]
      end // end of [intlst_cons]
    | intlst_nil () => let
        prval REPnil () = pf1
      in
        if c > 0 then aux1 (pf2 | ds2) else (pf2 | ds2)
      end // end of [intlst_nil]
  // end of [aux2]
} // end of [add_intlst_intlst]

(* ****** ****** *)

datatype POW2 (int, int) =
  | POW2bas (0, 1)
  | {n:nat} {p:int} POW2ind (n+1, 2*p) of POW2 (n, p)
// end of [POW2]

fun pow2 {n:nat} .<n>. (n: int n)
  :<> [ds:intlst;p:int] (POW2 (n, p), REP (ds, p) | intlst ds) =
  if n > 0 then let
    val (pf1, pf2 | ds) = pow2 (n-1)
    val (pf2 | ds) = add_intlst_intlst (pf2, pf2 | ds, ds)
  in
    (POW2ind (pf1), pf2 | ds)
  end else (
    POW2bas (), REPcons (REPnil) | intlst_cons (1, intlst_nil)
  ) // end of [if]
// end of [pow2]

fun p16 {n:nat} .<>. (n: int n):<>
  [p:int;ds:intlst;t:int] (POW2 (n, p), REP (ds, p), SUM (ds, t) | int t) = let
  val (pf1, pf2 | ds) = pow2 (n)
  val (pf3 | res) = sum (ds)
in
  (pf1, pf2, pf3 | res)
end // end of [p16]

(* ****** ****** *)

implement main () = () where {
  val (_, _, _ | ans) = p16 (1000)
  val () = assert_errmsg (ans = 1366, #LOCATION)
  val () = (print "the sum of all the digits of 2^1000 is "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem16-hwxi2.dats] *)
