(*
** A verified implementation of mergesort on lists
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January 4, 2011
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil
stadef cons = ilist_cons

(* ****** ****** *)

staload "libats/SATS/gflist_vt.sats"
macdef nil () = gflist_vt_nil ()
macdef cons (x, xs) = gflist_vt_cons (,(x), ,(xs))

(* ****** ****** *)

typedef lte (a:viewt@ype) =
  {x1,x2:int} (&elt (a, x1), &elt (a, x2)) -> bool (x1 <= x2)
// end of [lte]

(* ****** ****** *)

stadef ORD = ISORD
stadef PERM = PERMUTE
absprop SORT (xs: ilist, ys: ilist) // [ys] is sorted version of [xs]

(* ****** ****** *)

extern
prfun sort_singnil
  {xs:ilist} {n:nat | n <= 1} (pf: LENGTH (xs, n)): SORT (xs, xs)
// end of [sort_singnil]

(* ****** ****** *)

fun{a:viewt@ype}
split {xs:ilist} {n,i:nat | i <= n} .<i>. (
  pflen: LENGTH (xs, n) | xs: &gflist_vt (a, xs) >> gflist_vt (a, xs1), i: int i
) : #[xs1,xs2:ilist] (APPEND (xs1, xs2, xs), LENGTH (xs1, i) | gflist_vt (a, xs2)) =
  if i > 0 then let
    prval LENGTHcons (pflen) = pflen
    val gflist_vt_cons (_, !p_xs) = xs
    val (pfapp, pf1len | xs2) = split (pflen | !p_xs, i-1)
    prval () = fold@ (xs)
  in
    (APPENDcons (pfapp), LENGTHcons (pf1len) | xs2)
  end else let
    val xs2 = xs
    val () = xs := nil ()
    prval pfapp = append_unit1 ()
  in
    (pfapp, LENGTHnil () | xs2)
  end // end of [if]
// end of [split]

(* ****** ****** *)

viewtypedef gflist0_vt (a:viewt@ype) = gflist_vt (a, nil)

(* ****** ****** *)

absprop UNION (
  ys1: ilist, ys2: ilist, res: ilist
) // end of [absprop]

extern
prfun union_commute {ys1,ys2:ilist} {ys:ilist}
  (pf: UNION (ys1, ys2, ys)): UNION (ys2, ys1, ys)

extern
prfun union_nil1 {ys:ilist} (): UNION (nil, ys, ys)
extern
prfun union_nil2 {ys:ilist} (): UNION (ys, nil, ys)

extern
prfun union_cons1 {y:int} {ys1,ys2:ilist} {ys:ilist}
  (pf: UNION (ys1, ys2, ys)): UNION (cons (y, ys1), ys2, cons (y, ys))
extern
prfun union_cons2 {y:int} {ys1,ys2:ilist} {ys:ilist}
  (pf: UNION (ys1, ys2, ys)): UNION (ys1, cons (y, ys2), cons (y, ys))

extern
prfun isord_union_cons
  {y1,y2:int | y1 <= y2}
  {ys1,ys2:ilist} {ys:ilist} (
  pf1: ORD (cons (y1, ys1)), pf2: ORD (cons (y2, ys2))
, pf3: UNION (ys1, cons (y2, ys2), ys), pf4: ORD (ys)
) : ORD (cons (y1, ys))

(* ****** ****** *)

fun{a:viewt@ype}
merge {ys1,ys2:ilist} (
  pf1ord: ORD (ys1), pf2ord: ORD (ys2)
| ys1: gflist_vt (a, ys1), ys2: gflist_vt (a, ys2)
, lte: lte (a)
, ys: &gflist0_vt (a)? >> gflist_vt (a, ys)
) : #[ys:ilist] (UNION (ys1, ys2, ys), ORD (ys) | void) =
  case+ ys1 of
  | gflist_vt_cons (
      !p_y1, !p_ys1
    ) => (case+ ys2 of
    | gflist_vt_cons (
        !p_y2, !p_ys2
      ) =>
        if lte (!p_y1, !p_y2) then let
          val () = ys := ys1; val ys1 = !p_ys1
          prval () = fold@ (ys2)
          prval ISORDcons (pf1ord1, _) = pf1ord
          val (pfuni, pford | ()) = merge (pf1ord1, pf2ord | ys1, ys2, lte, !p_ys1)
          prval pford = isord_union_cons (pf1ord, pf2ord, pfuni, pford)
          prval () = fold@ (ys)
          prval pfuni = union_cons1 (pfuni)
        in
          (pfuni, pford | ())
        end else let
          prval () = fold@ (ys1)
          val () = ys := ys2; val ys2 = !p_ys2
          prval ISORDcons (pf2ord1, _) = pf2ord
          val (pfuni, pford | ()) = merge (pf1ord, pf2ord1 | ys1, ys2, lte, !p_ys2)
          prval pfuni = union_commute (pfuni)
          prval pford = isord_union_cons (pf2ord, pf1ord, pfuni, pford)
          prval () = fold@ (ys)
          prval pfuni = union_cons1 (pfuni)
          prval pfuni = union_commute (pfuni)
        in
          (pfuni, pford | ())
        end // end of [if]
      // end of [gflist_vt_cons]
    | ~gflist_vt_nil () => let
        val () = fold@ (ys1); val () = ys := ys1 in (union_nil2 (), pf1ord | ())
      end // end of [gflist_nil]
    ) // end of [gflist_vt_cons]
  | ~gflist_vt_nil () => let
      val () = ys := ys2 in (union_nil1 (), pf2ord | ())
    end // end of [gflist_vt_nil]
// end of [merge]

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

fun{a:viewt@ype}
msort {xs:ilist} {n:nat} .<n>. (
  pflen: LENGTH (xs, n) | xs: gflist_vt (a, xs), n: int n, lte: lte a
) : [ys:ilist] (SORT (xs, ys) | gflist_vt (a, ys)) =
  if n >= 2 then let
    val n2 = n/2
    var xs = xs
    val (pfapp, pf1len | xs2) = split (pflen | xs, n2)
    val xs1 = xs
    prval pf2len = length_istot ()
    prval pflen_alt = append_length_lemma (pfapp, pf1len, pf2len)
    prval () = length_isfun (pflen, pflen_alt)
    val (pf1srt | ys1) = msort (pf1len | xs1, n2, lte)
    prval pf1ord = SORT2ORD (pf1srt)
    prval pf1perm = SORT2PERM (pf1srt)
    val (pf2srt | ys2) = msort (pf2len | xs2, n-n2, lte)
    prval pf2ord = SORT2ORD (pf2srt)
    prval pf2perm = SORT2PERM (pf2srt)
    val (pfuni, pford | ()) = merge (pf1ord, pf2ord | ys1, ys2, lte, xs)
    prval pfperm = lemma (pfapp, pf1perm, pf2perm, pfuni) where {
      extern prfun lemma {xs1,xs2:ilist} {xs:ilist} {ys1,ys2:ilist} {ys:ilist} (
        pfapp: APPEND (xs1, xs2, xs), pf1: PERM (xs1, ys1), pf2: PERM (xs2, ys2), pf4: UNION (ys1, ys2, ys)
      ) : PERM (xs, ys)
    } // end of [prval]
    prval pfsrt = ORDPERM2SORT (pford, pfperm)
  in
    (pfsrt | xs)
  end else (sort_singnil (pflen) | xs)
// end of [msort]

(* ****** ****** *)

extern
fun{a:viewt@ype}
mergesort {xs:ilist} (
  xs: gflist_vt (a, xs), lte: lte a
) : [ys:ilist] (SORT (xs, ys) | gflist_vt (a, ys))

implement{a}
mergesort (xs, lte) = let
  val (pflen | n) = gflist_vt_length<a> (xs)
in
   msort<a> (pflen | xs, n, lte)
end // end of [mergesort]

(* ****** ****** *)

(* end of [mergesort_lst.dats] *)
