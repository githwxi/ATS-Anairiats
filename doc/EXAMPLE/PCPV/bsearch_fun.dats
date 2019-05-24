(*
** A verified implementation of binary search
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January 9, 2011
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil
stadef cons = ilist_cons

(* ****** ****** *)

absprop P (i:int, x:int)

(* ****** ****** *)

extern
prfun isordp
  {i1,i2:int | i1 <= i2} {x1,x2:int}
  (pf1: P (i1, x1), pf2: P (i2, x2)): [x1 <= x2] void
// end of [isordp]

(* ****** ****** *)

(*
{i:int | lb <= i; i <= i0} {x:int} (pf: P (i, x)): [x <= x0] void
{i:int | i0 <  i; i <= ub} {x:int} (pf: P (i, x)): [x0 <  x] void
*)

absprop BSEARCH (
  i0: int, x0: int, l: int, u: int
) // end of [BSEARCH]

(* ****** ****** *)

abst@ype E (a:t@ype, x:int)

typedef ordfun (a:t@ype) =
  {i:int} int (i) -> [x:int] (P (i, x) | E (a, x))
// end of [ordfun]

extern
fun{a:t@ype}
bsearch_fun {x0:int} {l,u:int} (
  f: ordfun a, x0: E (a, x0), l: int l, u: int u
) : [i0:int] (BSEARCH (i0, x0, l, u) | int i0)
// end of [bsearch_fun]

(* ****** ****** *)

(* end of [bsearch_fun.dats] *)