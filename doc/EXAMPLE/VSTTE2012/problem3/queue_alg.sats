(*
**
** An Example of Queue Algebra
** See Section 8.5.3 in Dines Bjorner's SE book
**
*)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil // creating a shorthand
stadef cons = ilist_cons // creating a shorthand

(* ****** ****** *)

dataprop EMPTY (ilist) = EMPTY (nil)

(* ****** ****** *)

dataprop
IS_EMPTY (ilist, bool) =
  | IS_EMPTY_nil (nil, true)
  | {x:int} {xs:ilist} IS_EMPTY_cons (cons (x, xs), false)
// end of [IS_EMPTY]

(* ****** ****** *)
//
// ENQUE (x, xs1, xs2) means that x :: xs1 = xs2 // [x] the last element
//
dataprop
ENQUE (int, ilist, ilist) =
  {x:int} {xs:ilist} ENQUE (x, xs, cons (x, xs))
// end of [ENQUE]

(* ****** ****** *)
//
// DEQUE (xs1, xs2, x) means that xs1 = xs2 @ [x] // [x] the first element
//
dataprop
DEQUE (ilist, ilist, int) =
  | {x0:int} {xs1,xs2:ilist} {x:int}
    DEQUE_cons (cons (x0, xs1), cons (x0, xs2), x) of DEQUE (xs1, xs2, x)
  | {x:int} DEQUE_nil (cons (x, nil), nil, x)
// end of [DEQUE]

//
// HQ (xs, x) means that [x] is the first element in [xs]
//
propdef HQ (xs:ilist, x:int) = [xs1:ilist] DEQUE (xs, xs1, x)
//
// RQ (xs, xs1) means that [xs1] is the tail of [xs]
//
propdef RQ (xs:ilist, xs1:ilist) = [x:int] DEQUE (xs, xs1, x)

(* ****** ****** *)

prfun DEQUE_isfun1 {xs:ilist} {x1,x2:int;xs1,xs2:ilist}
  (pf1: DEQUE (xs, xs1, x1), pf2: DEQUE (xs, xs2, x2)): [x1==x2] void
// end of [DEQUE_isfun1]

(* ****** ****** *)

(* end of [queue_alg.sats] *)
