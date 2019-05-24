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

dataprop EMPTY (ilist) = EMPTY (nil)

(* ****** ****** *)

dataprop
IS_EMPTY (ilist, bool) =
  | IS_EMPTY_nil (nil, true)
  | {x:int} {xs:ilist} IS_EMPTY_cons (cons (x, xs), false)
// end of [IS_EMPTY]

(* ****** ****** *)

dataprop
ENQUE (int, ilist, ilist) =
  {x:int} {xs:ilist} ENQUE (x, xs, cons (x, xs))
// end of [ENQUE]

dataprop
DEQUE (ilist, ilist, int) =
  | {x0:int} {xs1,xs2:ilist} {x:int}
    DEQUE_cons (cons (x0, xs1), cons (x0, xs2), x) of DEQUE (xs1, xs2, x)
  | {x:int} DEQUE_nil (cons (x, nil), nil, x)
// end of [DEQUE]

prfun DEQUE_isfun1 {xs:ilist} {x1,x2:int;xs1,xs2:ilist}
  (pf1: DEQUE (xs, xs1, x1), pf2: DEQUE (xs, xs2, x2)): [x1==x2] void
// end of [DEQUE_isfun1]

(* ****** ****** *)

(* end of [queue_alg.sats] *)
