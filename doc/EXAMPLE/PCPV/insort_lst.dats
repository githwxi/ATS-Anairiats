(*
** A verified implementation of insertion sort on lists
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December 25, 2010
*)

(* ****** ****** *)

(*
//
// HX: This is a standard implementation of insertion sort
//
fun{a:t@ype}
insort {n:nat}
  (xs: list (a, n), lte: (a, a) -> bool): list (a, n) = let
  fun ins {n:nat}
    (x: a, xs: list (a, n), lte: (a, a) -> bool): list (a, n+1) =
    case xs of
    | list_cons (x1, xs1) =>
        if lte (x, x1)
          then list_cons (x, xs) else list_cons (x1, ins (x, xs1, lte))
        // end of [if]
    | list_nil () => list_cons (x, list_nil ())
  // end of [ins]
in
  case xs of
  | list_cons (x, xs1) => ins (x, insort (xs1, lte), lte)
  | list_nil () => list_nil ()
end // end of [insort]
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil
stadef cons = ilist_cons

(* ****** ****** *)

staload "libats/SATS/gflist.sats"
macdef nil () = gflist_nil ()
macdef cons (x, xs) = gflist_cons (,(x), ,(xs))

(* ****** ****** *)

typedef lte (a:t@ype) =
  {x1,x2:int} (elt (a, x1), elt (a, x2)) -> bool (x1 <= x2)
// end of [lte]

(* ****** ****** *)

absprop ORD (xs: ilist) // [xs] is ordered
absprop PERM (xs: ilist, ys: ilist) // [xs] is a permutation of [ys]
absprop SORT (xs: ilist, ys: ilist) // [ys] is sorted version of [xs]

(* ****** ****** *)

extern
prfun SORT2ORD {xs,ys:ilist} (pf: SORT(xs, ys)): ORD (ys)

extern
prfun SORT2PERM {xs,ys:ilist} (pf: SORT(xs, ys)): PERM (xs, ys)

extern
prfun ORDPERM2SORT
  {xs,ys:ilist} (pf1: ORD (ys), pf2: PERM (xs, ys)): SORT (xs, ys)
// end of [ORDPERM2SORT]

(* ****** ****** *)

extern
prfun SORT_nil (): SORT (nil, nil)
extern
prfun SORT_sing {x:int} (): SORT (cons (x, nil), cons (x, nil))

(* ****** ****** *)

extern
prfun ORD_tail {y:int} {ys:ilist} (pf: ORD (cons (y, ys))): ORD (ys)

extern
prfun ORD_ins
  {x:int} {y1:int | x <= y1} {ys1:ilist}
  (pf: ORD (cons (y1, ys1))): ORD (cons (x, cons (y1, ys1)))
// end of [ORD_ins]

(* ****** ****** *)

extern
prfun PERM_refl {xs:ilist} (): PERM (xs, xs)
extern
prfun PERM_tran {xs,ys,zs:ilist}
  (pf1: PERM (xs, ys), pf2: PERM (ys, zs)): PERM (xs, zs)
extern
prfun PERM_cons {x:int} {xs1,xs2:ilist}
  (pf: PERM (xs1, xs2)): PERM (cons (x, xs1), cons (x, xs2))

(* ****** ****** *)

extern
prfun SORT_ins
  {x:int} {y1:int | x > y1} {ys1,ys2:ilist}
  (pf1: ORD (cons (y1, ys1)), pf2: SORT (cons (x, ys1), ys2))
  : SORT (cons (x, cons (y1, ys1)), cons (y1, ys2))
// end of [SORT_ins]

(* ****** ****** *)

fun{a:t@ype} insort
  {xs:ilist} (xs: gflist(a, xs), lte: lte(a))
  : [ys:ilist] (SORT (xs, ys) | gflist(a, ys)) = let
  fun ins {x:int} {ys1:ilist} (
    pford: ORD (ys1) |
    x: elt(a, x), ys1: gflist(a, ys1), lte: lte(a)
  ) : [ys2:ilist] (SORT (cons (x, ys1), ys2) | gflist (a, ys2)) =
    case ys1 of
    | gflist_cons (y1, ys10) =>
        if lte (x, y1) then let
          prval pford = ORD_ins {x} (pford)
          prval pfperm = PERM_refl ()
          prval pfsrt = ORDPERM2SORT (pford, pfperm)
        in
          (pfsrt | cons (x, ys1))
        end else let
          prval pford1 = ORD_tail (pford)
          val (pfsrt1 | ys20) = ins (pford1 | x, ys10, lte)
          prval pfsrt2 = SORT_ins {x} (pford, pfsrt1)
        in
          (pfsrt2 | cons (y1, ys20))
        end // end of [if]
    | gflist_nil () => (SORT_sing () | cons (x, nil ()))
  // end of [ins]
in
  case xs of
  | gflist_cons (x, xs1) => let
      val (pfsrt1 | ys1) = insort (xs1, lte)
      prval pford1 = SORT2ORD (pfsrt1)
      prval pfperm1 = SORT2PERM (pfsrt1)
      prval pfperm1_cons = PERM_cons (pfperm1)
      val (pfsrt2 | ys2) = ins (pford1 | x, ys1, lte)
      prval pford2 = SORT2ORD (pfsrt2)
      prval pfperm2 = SORT2PERM (pfsrt2)
      prval pfsrt3 = ORDPERM2SORT (pford2, PERM_tran (pfperm1_cons, pfperm2))
    in
      (pfsrt3 | ys2)
    end // end of [intlist_cons]
  | gflist_nil () => (SORT_nil () | nil ())
end // end of [insort]

(* ****** ****** *)

(* end of [insort_lst.dats] *)
