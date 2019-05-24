(*
** A verified implementation of binary search
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January 1, 2011
*)

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

(*
absprop LTB (x:int, xs:ilist)
absprop GTEB (xs:ilist, x:int)

propdef
BSEARCH (xs:ilist, x0:int, i:int) = [xsf,xsb:ilist] (
  LENGTH (xsf, i), APPEND (xsf, xsb, xs), GTEB (xsf, x0), LTB (x0, xsb)
) // end of [BSEARCH]
*)
absprop BSEARCH (xs:ilist, x0:int, i:int)

(* ****** ****** *)

extern
prfun bsearch_ind_isnat
  {xs:ilist} {x0:int} {i:int} (pf: BSEARCH (xs, x0, i)): [i>=0] void
// end of [bsearch_ind_isnat]

extern prfun bsearch_nil {x0:int} (): BSEARCH (nil, x0, 0)

extern
prfun bsearch_left
  {x0:int}
  {xs:ilist}
  {xs1:ilist}
  {x:int | x0 < x}
  {xs2:ilist}
  {i:int} (
  pf0: ISORD (xs)
, pf1: APPEND (xs1, cons (x, xs2), xs), pf2: BSEARCH (xs1, x0, i)
) : BSEARCH (xs, x0, i)

extern
prfun bsearch_right
  {x0:int}
  {xs:ilist}
  {xs1:ilist}
  {x:int | x0 >= x}
  {xs2:ilist}
  {n1:int} {i:int} (
  pf0: ISORD (xs)
, pf1: APPEND (xs1, cons (x, xs2), xs), pf2: LENGTH (xs1, n1), pf3: BSEARCH (xs2, x0, i)
) : BSEARCH (xs, x0, n1+1+i)

(* ****** ****** *)

extern
prfun isord_append_lemma1 {xs:ilist} {xs1,xs2:ilist}
  (pford: ISORD xs, pfapp: APPEND (xs1, xs2, xs)): ISORD (xs1)
extern
prfun isord_append_lemma2 {xs:ilist} {xs1,xs2:ilist}
  (pford: ISORD xs, pfapp: APPEND (xs1, xs2, xs)): ISORD (xs2)

(* ****** ****** *)

fun{a:t@ype}
bsearch {xs:ilist}
  {x0:int} {n:nat} {l:addr} .<n>. (
  pford: ISORD (xs)
, pflen: LENGTH (xs, n)
, pfarr: !gfarray_v (a, xs, l)
| p: ptr l, x0: &elt (a, x0), n: int n, cmp: cmp(a)
) : [i,ofs:int] (MUL (i, sizeof(a), ofs), BSEARCH (xs, x0, i) | ptr (l+ofs)) = let
  typedef res_t = [i,ofs:int] (
    MUL (i, sizeof(a), ofs), BSEARCH (xs, x0, i) | ptr (l+ofs)
  ) // end of [res_t]
in
  if n > 0 then let
    val n2 = n/2
    val tsz = sizeof<a>
    val tsz = int1_of_size1 (tsz)
    val (pfmul_nsz2 | nsz2) = n2 imul2 tsz
    prval [xs1,xs2:ilist] (
      pflen_xs1, pfapp_xs1_xs2, pfarr_xs1, pfarr_xs2
    ) = gfarray_v_split {a} (pflen, pfmul_nsz2, pfarr)
//
    prval pflen_xs2 = length_istot {xs2} ()
    prval pflen_alt = append_length_lemma (pfapp_xs1_xs2, pflen_xs1, pflen_xs2)
    prval () = length_isfun (pflen, pflen_alt)
    prval LENGTHcons {x} {xs21} (pflen_xs21) = pflen_xs2
//
    prval gfarray_v_cons (pfat_x, pfarr_xs21) = pfarr_xs2
    val p1 = p + nsz2
    val sgn = cmp {x0,x} (x0, !p1)
//
    val res = (
      if sgn < 0 then let
        prval pford_xs1 =
          isord_append_lemma1 (pford, pfapp_xs1_xs2)
        val (pfmul_xs1f, pfsrch_xs1 | p_res) = bsearch
          (pford_xs1, pflen_xs1, pfarr_xs1 | p, x0, n2, cmp)
        prval pfsrch_xs =
          bsearch_left (pford, pfapp_xs1_xs2, pfsrch_xs1)
      in
        (pfmul_xs1f, pfsrch_xs | p_res)
      end else let
        prval pford_xs2 = isord_append_lemma2 (pford, pfapp_xs1_xs2)
        prval ISORDcons (pford_xs21, _) = pford_xs2
        val p21 = p1 + tsz
        val (pfmul_xs21f, pfsrch_xs21 | p21_res) = bsearch
          (pford_xs21, pflen_xs21, pfarr_xs21 | p21, x0, n-1-n2, cmp)
        prval pfsrch_xs =
          bsearch_right (pford, pfapp_xs1_xs2, pflen_xs1, pfsrch_xs21)
        prval pfmul_xsf =
          mul_distribute2 (pfmul_nsz2, mul_add_const {1} (pfmul_xs21f))
      in
        (pfmul_xsf, pfsrch_xs | p21_res)
      end // end of [val]
    ) : res_t // end of [val]
//
    prval pfarr_xs2 = gfarray_v_cons {a} (pfat_x, pfarr_xs21)
    prval (pfapp_alt, pfarr_alt) =
      gfarray_v_unsplit {a} (pflen_xs1, pfmul_nsz2, pfarr_xs1, pfarr_xs2)
    prval ILISTEQ () = append_isfun (pfapp_xs1_xs2, pfapp_alt)
    prval () = pfarr := pfarr_alt
//
  in
    res
  end else let
    prval LENGTHnil () = pflen
    prval pfsrch = bsearch_nil {x0} ()
  in
    (MULbas (), pfsrch | p)
  end // end of [if]
end // end of [bsearch]

(* ****** ****** *)

(* end of [bsearch_arr.dats] *)
