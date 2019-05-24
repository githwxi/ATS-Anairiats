(*
** A verified implementation of quicksort on lists
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December 26, 2010
*)

(* ****** ****** *)

(*

//
// HX: This is a standard implementation of quicksort
//

extern
fun{a:t@ype}
append {m,n:nat}
  (xs1: list (a, m), xs2: list (a, n)): list (a, m+n)
// end of [append]

fun{a:t@ype}
qsrt {n:nat}
  (xs: list (a, n), lte: lte a) : list (a, n) =
  case+ xs of
  | list_cons (x, xs) => part (x, xs, lte, list_nil (), list_nil ())
  | list_nil () => list_nil ()
// end of [qsrt]

and part {p:nat} {q,r:nat} (
  x0: a, xs: list (a, p), lte: lte(a), ys: list (a, q), zs: list (a, r)
) : list (a, p+q+r+1) =
  case+ xs of
  | list_cons (x, xs) =>
      if lte (x, x0) then
        part (x0, xs, lte, list_cons (x, ys), zs)
      else
        part (x0, xs, lte, ys, list_cons (x, zs))
      // end of [if]        
  | list_nil () => let
      val ys = qsrt (ys, lte) and zs = qsrt (zs, lte)
    in
      append (ys, list_cons (x0, zs))
    end // end of [list_nil]
// end of [part]

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

macdef append = gflist_append

(* ****** ****** *)

typedef lte (a:t@ype) =
  {x1,x2:int} (elt (a, x1), elt (a, x2)) -> bool (x1 <= x2)
// end of [lte]

(* ****** ****** *)

stadef ORD = ISORD
stadef PERM = PERMUTE
absprop SORT (xs: ilist, ys: ilist) // [ys] is sorted version of [xs]

(* ****** ****** *)

absprop LB (x:int, xs:ilist)
absprop UB (x:int, xs:ilist)
absprop UNION4 (x:int, xs:ilist, ys:ilist, zs:ilist, res:ilist)

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

extern prfun LB_nil {x:int} (): LB (x, nil)
extern prfun UB_nil {x:int} (): UB (x, nil)

extern prfun LB_cons {x0:int}
  {x:int | x0 <= x} {xs:ilist} (pf: LB (x0, xs)): LB (x0, cons (x, xs))
extern prfun UB_cons {x0:int}
  {x:int | x0 >= x} {xs:ilist} (pf: UB (x0, xs)): UB (x0, cons (x, xs))

extern prfun LB_perm {x:int} {xs1,xs2:ilist} 
  (pf1: PERM (xs1, xs2), pf2: LB (x, xs1)): LB (x, xs2)
extern prfun UB_perm {x:int} {xs1,xs2:ilist} 
  (pf1: PERM (xs1, xs2), pf2: UB (x, xs1)): UB (x, xs2)

(* ****** ****** *)

extern
prfun UNION4_perm {x:int} {xs:ilist} {res:ilist}
  (pf: UNION4 (x, xs, nil, nil, res)): PERM (cons (x, xs), res)

extern
prfun UNION4_mov1
  {x0:int} {x:int} {xs:ilist} {ys,zs:ilist} {res:ilist}
  (pf: UNION4 (x0, xs, cons (x, ys), zs, res)): UNION4 (x0, cons (x, xs), ys, zs, res)
extern
prfun UNION4_mov2
  {x0:int} {x:int} {xs:ilist} {ys,zs:ilist} {res:ilist}
  (pf: UNION4 (x0, xs, ys, cons (x, zs), res)): UNION4 (x0, cons (x, xs), ys, zs, res)

(* ****** ****** *)

extern
prfun APPEND_ord
  {x:int}
  {ys,zs:ilist}
  {res:ilist} (
  pf1: UB (x, ys), pf2: LB (x, zs)
, pf3: ORD (ys), pf4: ORD (zs)
, pf5: APPEND (ys, cons (x, zs), res)
) : ORD (res)

extern
prfun APPEND_union4
  {x:int} {ys,ys1:ilist} {zs,zs1:ilist} {res:ilist} (
  pf1: PERM (ys, ys1), pf2: PERM (zs, zs1), pf3: APPEND (ys1, cons (x, zs1), res)
) : UNION4 (x, nil, ys, zs, res)

(* ****** ****** *)

fun{a:t@ype}
qsrt {xs:ilist} (
  xs: gflist (a, xs), lte: lte a
) : [ys:ilist] (SORT (xs, ys) | gflist (a, ys)) =
  case+ xs of
  | gflist_cons (x, xs) => let
      val (pford, pfuni | res) = part (UB_nil (), LB_nil () | x, xs, lte, nil (), nil ())
      prval pfperm = UNION4_perm (pfuni)
    in
      (ORDPERM2SORT (pford, pfperm) | res)
    end // end of [gflist_cons]
  | gflist_nil () => (SORT_nil () | nil ())
// end of [qsrt]

and part
  {x0:int} {xs:ilist} {ys,zs:ilist} (
  pf1: UB (x0, ys), pf2: LB (x0, zs)
| x0: elt (a, x0), xs: gflist (a, xs)
, lte: lte(a), ys: gflist (a, ys), zs: gflist (a, zs)
) : [res:ilist] (
  ORD (res), UNION4 (x0, xs, ys, zs, res) | gflist (a, res)
) =
  case+ xs of
  | gflist_cons (x, xs) =>
      if lte (x, x0) then let
        prval pf1 = UB_cons (pf1)
        val (pford, pfuni | res) = part (pf1, pf2 | x0, xs, lte, cons (x, ys), zs)
        prval pfuni = UNION4_mov1 (pfuni)
      in
        (pford, pfuni | res)
      end else let
        prval pf2 = LB_cons (pf2)
        val (pford, pfuni | res) = part (pf1, pf2 | x0, xs, lte, ys, cons (x, zs))
        prval pfuni = UNION4_mov2 (pfuni)
      in
        (pford, pfuni | res)
      end // end of [if]        
    // end of [gflist_cons]
  | gflist_nil () => let
      val (pfsrt1 | ys) = qsrt (ys, lte)
      val (pfsrt2 | zs) = qsrt (zs, lte)
      val (pfapp | res) = append (ys, cons (x0, zs))
      prval pford1 = SORT2ORD (pfsrt1)
      prval pford2 = SORT2ORD (pfsrt2)
      prval pfperm1 = SORT2PERM (pfsrt1)
      prval pfperm2 = SORT2PERM (pfsrt2)
      prval pf1 = UB_perm (pfperm1, pf1)
      prval pf2 = LB_perm (pfperm2, pf2)
      prval pford = APPEND_ord (pf1, pf2, pford1, pford2, pfapp)
      prval pfuni = APPEND_union4 (pfperm1, pfperm2, pfapp)
    in
      (pford, pfuni | res)
    end // end of [gflist_nil]
// end of [part]

(* ****** ****** *)

(* end of [quicksort_lst.dat] *)
