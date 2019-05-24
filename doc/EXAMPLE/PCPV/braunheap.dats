(*
** A verified implementation of binary heap based on Braun trees
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January 5, 2011
*)

(* ****** ****** *)

staload "libats/SATS/itreep.sats"
stadef nil = itree_nil
stadef cons = itree_cons

(* ****** ****** *)

staload "libats/SATS/gftree.sats"

(* ****** ****** *)

macdef nil = gftree_nil
macdef cons (x, tl, tr) = gftree_cons (,(x), ,(tl), ,(tr))

(* ****** ****** *)

typedef lte (a:t@ype) =
  {x1,x2:int} (elt (a, x1), elt (a, x2)) -> bool (x1 <= x2)
// end of [lte]

(* ****** ****** *)

extern
prfun isheap_sing {x:int} (): ISHEAP (cons (x, nil, nil))

(* ****** ****** *)

dataprop ISBRAUN (itree) =
  | ISBRAUNnil (itree_nil)
  | {x:int} {tl,tr:itree} {nl,nr:nat | nr <= nl; nl <= nr+1}
    ISBRAUNcons (
      itree_cons (x, tl, tr)
    ) of (
      ISBRAUN (tl), ISBRAUN (tr), TREESZ (tl, nl), TREESZ (tr, nr)
    ) // end of [ISBRAUNcons]
// end of [ISBRAUN]

extern
prfun isbraun_sing {x:int} (): ISBRAUN (cons (x, nil, nil))

(* ****** ****** *)

absprop INSERT (
  t0: itree, x: int, t1: itree
) // |t0| ++ {x} = |t1|

extern
prfun insert_nil {x:int} (): INSERT (nil, x, cons (x, nil, nil))

extern
prfun insert_cons_commute
  {x:int} {t0:itree} {y:int} {t1l,t1r:itree}
  (pf: INSERT (t0, x, cons (y, t1l, t1r))): INSERT (t0, x, cons (y, t1r, t1l))

extern
prfun insert_left {x:int} {y:int} {t0l,t0r:itree} {t1l:itree}
  (pf: INSERT (t0l, x, t1l)): INSERT (cons (y, t0l, t0r), x, cons (y, t1l, t0r))
// end of [insert_left]

extern
prfun insert_left2 {x:int} {y:int} {t0l,t0r:itree} {t1l:itree}
  (pf: INSERT (t0l, x, t1l)): INSERT (cons (x, t0l, t0r), y, cons (y, t1l, t0r))
// end of [insert_left2]

extern
prfun insert_right {x:int} {y:int} {t0l,t0r:itree} {t1r:itree}
  (pf: INSERT (t0r, x, t1r)): INSERT (cons (y, t0l, t0r), x, cons (y, t0l, t1r))
// end of [insert_right]

extern
prfun insert_right2 {x:int} {y:int} {t0l,t0r:itree} {t1r:itree}
  (pf: INSERT (t0r, x, t1r)): INSERT (cons (x, t0l, t0r), y, cons (y, t0l, t1r))
// end of [insert_right2]

extern
prfun insert_size_lemma {x:int} {t0,t1:itree} {n:int}
  (pf1: INSERT (t0, x, t1), pf2: TREESZ (t0, n)): TREESZ (t1, n+1)
// end of [insert_size_lemma]

extern
prfun insert_lteb_lemma
  {x0:int} {x:int | x0 <= x} {t0,t1:itree}
  (pf1: INSERT (t0, x, t1), pf2: LTEB (x0, t0)): LTEB (x0, t1)
// end of [insert_lteb_lemma]

(* ****** ****** *)

extern
fun{a:t@ype}
braunheap_insert {x0:int} {t0:itree} (
  pfbt: ISBRAUN (t0), pfhp: ISHEAP (t0)
| t: gftree (a, t0), x0: elt (a, x0), lte: lte a
) : [t1:itree] (INSERT (t0, x0, t1), ISBRAUN (t1), ISHEAP (t1) | gftree (a, t1))

implement{a}
braunheap_insert {x0} {t0}
  (pfbt, pfhp | t0, x0, lte) = case+ t0 of
  | gftree_nil () => let
      prval pfins = insert_nil {x0} ()
      prval pfbt_res = isbraun_sing {x0} ()
      prval pfhp_res = isheap_sing {x0} ()
    in
      (pfins, pfbt_res, pfhp_res | cons (x0, nil, nil))
    end // end of [gftree_nil]
  | gftree_cons {a} {x} {t0l,t0r} (x, t0l, t0r) => let
      prval ISBRAUNcons (pfbtl, pfbtr, pfszl, pfszr) = pfbt
      prval ISHEAPcons (pfhpl, pfhpr, pfltebl, pfltebr) = pfhp
    in
      if lte (x0, x) then let
        val [t1r:itree] (
          pfinsr, pfbtr_res, pfhpr_res | t1r
        ) = braunheap_insert (pfbtr, pfhpr | t0r, x, lte)
        prval pfszr_res = insert_size_lemma (pfinsr, pfszr)
        prval pfbt_res = ISBRAUNcons (pfbtr_res, pfbtl, pfszr_res, pfszl)
        prval pfltebl = lteb_dec (pfltebl)
        prval pfltebr_res = insert_lteb_lemma (pfinsr, pfltebr)
        prval pfltebr_res = lteb_dec (pfltebr_res)
        prval pfhp_res = ISHEAPcons {x0} (pfhpr_res, pfhpl, pfltebr_res, pfltebl)
//
        prval pfins = insert_right2 (pfinsr)
        prval pfins = insert_cons_commute (pfins)
//
      in
        (pfins, pfbt_res, pfhp_res | gftree_cons (x0, t1r, t0l))
      end else let
        val [t1r:itree] (
          pfinsr, pfbtr_res, pfhpr_res | t1r
        ) = braunheap_insert (pfbtr, pfhpr | t0r, x0, lte)
        prval pfszr_res = insert_size_lemma (pfinsr, pfszr)
        prval pfbt_res = ISBRAUNcons (pfbtr_res, pfbtl, pfszr_res, pfszl)
        prval pfltebr_res = insert_lteb_lemma (pfinsr, pfltebr)
        prval pfhp_res = ISHEAPcons {x} (pfhpr_res, pfhpl, pfltebr_res, pfltebl)
//
        prval pfins = insert_right (pfinsr)
        prval pfins = insert_cons_commute (pfins)
//
      in
        (pfins, pfbt_res, pfhp_res | gftree_cons (x, t1r, t0l))
      end // end of [if]
    end // end of [gftree_cons]
// end of [brauntree_insert]

(* ****** ****** *)

(* end of [braunheap.dats] *)
