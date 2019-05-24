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

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil // creating a shorthand
stadef cons = ilist_cons // creating a shorthand

(* ****** ****** *)
//
// HX: none of the following dataprops are really needed;
// they are kept so that a direct correspondence to the
// original formulation in Bjorner's book can be readily
// noticed.
//
(* ****** ****** *)

// this specifies what EMPTY does
dataprop EMPTY (ilist) = EMPTY (nil)

// this specifies what IS_EMPTY does
dataprop
IS_EMPTY (ilist, bool) =
  | IS_EMPTY_nil (nil, true)
  | {x:int} {xs:ilist} IS_EMPTY_cons (cons (x, xs), false)
// end of [IS_EMPTY]

// this specifies what TOP does
dataprop TOP (ilist, int) =
  | {x:int} {xs:ilist} TOP (cons (x, xs), x)
// end of [TOP]

// this specifies what POP does
dataprop POP (ilist, ilist) =
  | {x:int} {xs:ilist} POP (cons (x, xs), xs)
// end of [POP]

// this specifies what PUSH does
dataprop PUSH (int, ilist, ilist) =
  | {x:int} {xs:ilist} PUSH (x, xs, cons (x, xs))
// end of [PUSH]

(* ****** ****** *)

(* end of [stack_alg.sats] *)
