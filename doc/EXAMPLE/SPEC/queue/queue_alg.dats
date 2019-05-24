(*
**
** An Example of Queue Algebra
** See Section 8.5.3 in Dines Bjorner's SE book
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2010
**
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil // creating a shorthand
stadef cons = ilist_cons // creating a shorthand

(* ****** ****** *)

staload "queue_alg.sats"

(* ****** ****** *)

propdef DQ (xs:ilist, x:int) = [xs1:ilist] DEQUE (xs, xs1, x)
propdef RQ (xs:ilist, xs1:ilist) = [x:int] DEQUE (xs, xs1, x)

(* ****** ****** *)

prfun lemma1 {x:int} {xs1,xs2:ilist} .<>.
  (pf: ENQUE (x, xs1, xs2)): IS_EMPTY (xs2, false) = let
  prval ENQUE () = pf
in
  IS_EMPTY_cons ()
end // end of [lemma1]
  
(* ****** ****** *)

prfun lemma2 {x:int} {xs1,xs2:ilist} .<>.
  (pf1: EMPTY (xs1), pf2: ENQUE (x, xs1, xs2)): DQ (xs2, x) = let
  prval EMPTY () = pf1
  prval ENQUE () = pf2
in
  DEQUE_nil ()
end // end of [lemma2]

(* ****** ****** *)

prfun lemma2 {x:int} {xs1,xs2:ilist} .<>.
  (pf1: EMPTY (xs1), pf2: ENQUE (x, xs1, xs2)): RQ (xs2, nil) = let
  prval EMPTY () = pf1
  prval ENQUE () = pf2
in
  DEQUE_nil ()
end // end of [lemma2]

(* ****** ****** *)

prfun lemma3
  {x1,x2:int}
  {xs1,xs2,xs3:ilist}
  {y1,y2:int} .<>. (
  pf1: ENQUE (x1, xs1, xs2)
, pf2: ENQUE (x2, xs2, xs3)
, pf3: DQ (xs2, y1)
, pf4: DQ (xs3, y2)
) : [y1==y2] void = let
  prval ENQUE () = pf1
  prval ENQUE () = pf2
  prval DEQUE_cons (pf41) = pf4
in
  DEQUE_isfun1 (pf3, pf41)
end // end of [lemma3]

(* ****** ****** *)

prfun lemma4
  {x1,x2:int}
  {xs1,xs2,xs3:ilist}
  {xs11,xs21:ilist} .<>. (
  pf1: ENQUE (x1, xs1, xs2) // xs2 = cons (x1, xs1) // not used
, pf2: ENQUE (x2, xs2, xs3) // xs3 = cons (x2, xs2) = x2::x1::xs1
, pf3: RQ (xs2, xs11) // xs2 = xs11@y
, pf4: ENQUE (x2, xs11, xs21)
) : RQ (xs3, xs21) = let
  prval ENQUE () = pf2
  prval ENQUE () = pf4
in
  DEQUE_cons (pf3)
end // end of [lemma4]

(* ****** ****** *)

prfun lemma5
  {x:int} {xs1,xs2:ilist} {y:int} {ys:ilist} .<>.
  (pf1: ENQUE (x, xs1, xs2), pf2: DEQUE (xs2, ys, y)): (RQ (xs2, ys), DQ (xs2, y)) =
  (pf2, pf2)
// end of [lemma5]

(* ****** ****** *)

(* end of [queue_alg.dats] *)
