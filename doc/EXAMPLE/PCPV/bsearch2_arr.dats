(*
** A verified implementation of binary search
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December 31, 2010
*)

(* ****** ****** *)
//
// HX:
// I think bsearch is significantly more difficult to verify
// than quicksort!
//
(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil
stadef cons = ilist_cons

(* ****** ****** *)

staload "libats/SATS/gfarray.sats"

(* ****** ****** *)

typedef cmp (a:viewt@ype) =
  {x1,x2:int} (&elt (a, x1), &elt (a, x2)) -> int (x1-x2)
// end of [lte]

(* ****** ****** *)

absprop LTB (x:int, xs:ilist)
absprop GTEB (xs:ilist, x:int)

propdef
BSEARCH (xs:ilist, x0:int, i:int) = [xsf,xsb:ilist] (
  LENGTH (xsf, i), APPEND (xsf, xsb, xs), GTEB (xsf, x0), LTB (x0, xsb)
) // end of [BSEARCH]

(* ****** ****** *)

prfun bsearch_ind_isnat
  {xs:ilist} {x0:int} {i:int} .<>.
  (pf: BSEARCH (xs, x0, i)): [i>=0] void = length_isnat (pf.0)
// end of [bsearch_ind_isnat]

(* ****** ****** *)

extern
prfun ltb_nil {x:int} (): LTB (x, nil)
extern
prfun gteb_nil {x:int} (): GTEB (nil, x)

(* ****** ****** *)

extern
prfun append_assoc_lemma1
  {xs12:ilist} {xs1,xs2:ilist}
  {xs1b,xs1f:ilist} {xs1b2:ilist} (
  pfapp: APPEND (xs1, xs2, xs12)
, pf1app: APPEND (xs1f, xs1b, xs1)
, pf2app: APPEND (xs1b, xs2, xs1b2)
) : APPEND (xs1f, xs1b2, xs12)

extern
prfun append_assoc_lemma2
  {xs12:ilist} {xs1,xs2:ilist}
  {xs2b,xs2f:ilist} {xs12f:ilist} (
  pfapp: APPEND (xs1, xs2, xs12)
, pf1app: APPEND (xs2f, xs2b, xs2)
, pf2app: APPEND (xs1, xs2f, xs12f)
) : APPEND (xs12f, xs2b, xs12)

extern
prfun isord_append_lemma1 {xs:ilist} {xs1,xs2:ilist}
  (pford: ISORD xs, pfapp: APPEND (xs1, xs2, xs)): ISORD (xs1)
extern
prfun isord_append_lemma2 {xs:ilist} {xs1,xs2:ilist}
  (pford: ISORD xs, pfapp: APPEND (xs1, xs2, xs)): ISORD (xs2)

(* ****** ****** *)

fun{a:t@ype}
bsearch {xs:ilist} {x0:int} {n:nat} {l:addr} .<n>. (
  pford: ISORD (xs)
, pflen: LENGTH (xs, n)
, pfarr: !gfarray_v (a, xs, l)
| p: ptr l, x0: &elt (a, x0), n: int n, cmp: cmp(a)
) : [i,ofs:int] (MUL (i, sizeof(a), ofs), BSEARCH (xs, x0, i) | ptr (l+ofs)) =
  if n > 0 then let
    val n2 = n/2
    val tsz = sizeof<a>
    val tsz = int1_of_size1 (tsz)
    val (pfmul_nsz2 | nsz2) = n2 imul2 tsz
    prval [xs1,xs2:ilist]
      (pflen_xs1, pfapp_xs1_xs2, pfarr_xs1, pfarr_xs2) = gfarray_v_split {a} (pflen, pfmul_nsz2, pfarr)
//
    prval pflen_xs2 = length_istot {xs2} ()
    prval pflen_alt = append_length_lemma (pfapp_xs1_xs2, pflen_xs1, pflen_xs2)
    prval () = length_isfun (pflen, pflen_alt)
    prval LENGTHcons _ = pflen_xs2
//
    prval pford_xs1 = isord_append_lemma1 (pford, pfapp_xs1_xs2)
    prval pford_xs2 = isord_append_lemma2 (pford, pfapp_xs1_xs2)
//
    stavar x: int
    prval gfarray_v_cons (pfat_x, pfarr_xs21) = pfarr_xs2
    val p1 = p + nsz2
    val sgn = cmp {x0,x} (x0, !p1)
//
  in
    if sgn < 0 then let
//
      val (pfmul_xs1f, pfsrch_xs1 | p_res) = bsearch (pford_xs1, pflen_xs1, pfarr_xs1 | p, x0, n2, cmp)
      prval (pflen_xs1f, pfapp_xs1f_xs1b, pfgteb_xs1f, pfltb_xs1b) = pfsrch_xs1
      stavar xs1f: ilist and xs1b: ilist
      prval pfapp_xs1f_xs1b = pfapp_xs1f_xs1b: APPEND (xs1f, xs1b, xs1)
      prval [xs1b2:ilist] pfapp_xs1b_xs2 = append_istot {xs1b, xs2} ()
      prval pfapp_xs1f_xs1b2 = append_assoc_lemma1 (pfapp_xs1_xs2, pfapp_xs1f_xs1b, pfapp_xs1b_xs2)
//
extern
prfun ltb_isord_lemma1
  {x0,x:int | x0 < x} {xs:ilist}
  (pf: ISORD (cons (x, xs))): LTB (x0, cons (x, xs))
// end of [ltb_isord_lemma1]
extern
prfun ltb_append_lemma1
  {x0:int} {xs1,xs2:ilist} {xs:ilist}
  (pf1: LTB (x0, xs1), pf2: LTB (x0, xs2), pf3: APPEND (xs1, xs2, xs)): LTB (x0, xs)
// end of [ltb_append_lemma1]
//
      prval pfltb_xs2 = ltb_isord_lemma1 (pford_xs2)
      prval pfltb_xs1b2 = ltb_append_lemma1 (pfltb_xs1b, pfltb_xs2, pfapp_xs1b_xs2)
//
      prval pfsrch_xs = (pflen_xs1f, pfapp_xs1f_xs1b2, pfgteb_xs1f, pfltb_xs1b2)
//
      prval pfarr_xs2 = gfarray_v_cons {a} (pfat_x, pfarr_xs21)
      prval (pfapp_alt, pfarr_alt) = gfarray_v_unsplit {a} (pflen_xs1, pfmul_nsz2, pfarr_xs1, pfarr_xs2)
      prval ILISTEQ () = append_isfun (pfapp_xs1_xs2, pfapp_alt)
      prval () = pfarr := pfarr_alt
    in
      (pfmul_xs1f, pfsrch_xs | p_res)
    end else let
//
      prval [xs1x:ilist] pfsnoc_xs1_x = snoc_istot {xs1} {x} ()
      prval pflen_xs1x = snoc_length_lemma (pfsnoc_xs1_x, pflen_xs1)
      prval pfapp_xs1x_xs21 = append_snoc_lemma (pfapp_xs1_xs2, pfsnoc_xs1_x)
//
extern
prfun gteb_isord_append_snoc_lemma1 {x0:int}
  {xs1:ilist} {x:int | x <= x0} {xs21:ilist} {xs1x:ilist} {xs:ilist} (
  pf1:ISORD (xs), pf2: APPEND (xs1, cons (x, xs21), xs), pf3: SNOC (xs1, x, xs1x)
) : GTEB (xs1x, x0) // end of [gteb_isord_append_snoc_lemma1]
//
      prval pfgteb_xs1x = gteb_isord_append_snoc_lemma1 {x0} (pford, pfapp_xs1_xs2, pfsnoc_xs1_x)
//
      val p21 = p1 + tsz
      prval LENGTHcons (pflen_xs21) = pflen_xs2
      prval ISORDcons (pford_xs21, _) = pford_xs2
      val (pfmul_xs21f, pfsrch_xs21 | p21_res) = bsearch (pford_xs21, pflen_xs21, pfarr_xs21 | p21, x0, n-1-n2, cmp)
//
      prval (pflen_xs21f, pfapp_xs21f_xs21b, pfgteb_xs21f, pfltb_xs21b) = pfsrch_xs21
      stavar xs21f: ilist and xs21b: ilist and xs21: ilist
      prval pfapp_xs21f_xs21b = pfapp_xs21f_xs21b: APPEND (xs21f, xs21b, xs21)
      prval [xs1x21f:ilist] pfapp_xs1x_xs21f = append_istot {xs1x, xs21f} ()
      prval pflen_xs1x21f = append_length_lemma (pfapp_xs1x_xs21f, pflen_xs1x, pflen_xs21f)
      prval pfapp_xs1x21f_xs2b = append_assoc_lemma2 (pfapp_xs1x_xs21, pfapp_xs21f_xs21b, pfapp_xs1x_xs21f)
//
extern
prfun gteb_append_lemma1
  {x0:int} {xs1,xs2:ilist} {xs:ilist}
  (pf1: GTEB (xs1, x0), pf2: GTEB (xs2, x0), pf3: APPEND (xs1, xs2, xs)): GTEB (xs, x0)
// end of [gteb_append_lemma1]
//
      prval pfgteb_xs1x21f = gteb_append_lemma1 (pfgteb_xs1x, pfgteb_xs21f, pfapp_xs1x_xs21f)
      prval pfsrch_xs = (pflen_xs1x21f, pfapp_xs1x21f_xs2b, pfgteb_xs1x21f, pfltb_xs21b)
      prval pfmul_xs1x = mul_add_const {1} (pfmul_nsz2)
      prval pfmul_xs1x2f = mul_distribute2 (pfmul_xs1x, pfmul_xs21f)
//
      prval pfarr_xs2 = gfarray_v_cons {a} (pfat_x, pfarr_xs21)
      prval (pfapp_alt, pfarr_alt) = gfarray_v_unsplit {a} (pflen_xs1, pfmul_nsz2, pfarr_xs1, pfarr_xs2)
      prval ILISTEQ () = append_isfun (pfapp_xs1_xs2, pfapp_alt)
      prval () = pfarr := pfarr_alt
    in
      (pfmul_xs1x2f, pfsrch_xs | p21_res)
    end // end of [if]
  end else let
    prval LENGTHnil () = pflen
    prval pflen_res = pflen
    prval pfapp_res = append_unit1 {nil} ()
    prval pfgteb_res = gteb_nil {x0} () and pfltb_res = ltb_nil {x0} ()
    prval pfsrch = (pflen_res, pfapp_res, pfgteb_res, pfltb_res)
  in
    (MULbas (), pfsrch | p)
  end // end of [if]

(* ****** ****** *)

(* end of [bsearch2_arr.dats] *)
