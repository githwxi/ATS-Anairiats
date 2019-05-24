(*
**
** An Example of Stack Algebra
** See Section 8.5.2 in Dines Bjorner's SE book
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December, 2010
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at run-time

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

staload "stack_alg.sats"

(* ****** ****** *)
//
// HX: none of the following lemmas are needed;
// they are kept so that a direct correspondence to the
// original formulation in Bjorner's book can be readily
// noticed.
//
(* ****** ****** *)

// this is a property that can be proven
prfun lemma1 {xs:ilist} .<>.
  (pf: EMPTY (xs)): IS_EMPTY (xs, true) =
  let prval EMPTY () = pf in IS_EMPTY_nil () end
// end of [lemma1]

// this is a property that can be proven
prfun lemma2
  {x:int} {xs1,xs2:ilist} .<>.
  (pf: PUSH (x, xs1, xs2)): TOP (xs2, x) =
  let prval PUSH () = pf in TOP () end
// end of [lemma2]

// this is a property that can be proven
prfun lemma3
  {x:int} {xs1,xs2:ilist} .<>.
  (pf: PUSH (x, xs1, xs2)): POP (xs2, xs1) =
  let prval PUSH () = pf in POP () end
// end of [lemma3]

(* ****** ****** *)

(* end of [stack_alg.dats] *)
