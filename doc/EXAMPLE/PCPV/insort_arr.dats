(*
** A verified implementation of insertion sort on arrays
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: December 27, 2010
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"

(* ****** ****** *)

(*
fun{a:t@ype}
insort
  {n:nat} {l:addr} (
  pf: !array_v (a, n, l)
| p: ptr l, n: int n, lte: (a, a) -> bool
) : void = let
//
  fun ins {n:nat} {l:addr} (
    pf1: a@l, pf2: array_v (a, n, l+sizeof(a))
  | p: ptr l, n: int n, lte: (a, a) -> bool
  ) : (array_v (a, n+1, l) | void) =
  if n > 0 then let
    val p1 = p + sizeof<a>
    prval (pf21, pf22) = array_v_uncons {a} (pf2)
    val x = !p
  in
    if x \lte !p1 then let
      prval pf2 = array_v_cons (pf21, pf22)
    in
      (array_v_cons (pf1, pf2) | ())
    end else let
      val () = !p := !p1
      val () = !p1 := x
      val (pf2 | ()) = ins (pf21, pf22 | p1, n-1, lte)
    in
      (array_v_cons (pf1, pf2) | ())
    end // end of [if]
  end else (array_v_cons (pf1, pf2) | ())
//
  fun loop {n1,n2:nat} {l:addr} {ofs:int} (
    pfmul: MUL (n1, sizeof(a), ofs)
  , pf1: array_v (a, n1, l), pf2: array_v (a, n2, l+ofs)
  | p: ptr (l+ofs), n1: int n1, n2: int n2, lte: (a, a) -> bool
  ) : (array_v (a, n1+n2, l) | void) =
  if n1 > 0 then let
    prval (pf11, pf12) = array_v_unextend {a} (pfmul, pf1)
    val p1 = p-sizeof<a>
    val (pf2 | ()) = ins (pf12, pf2 | p1, n2, lte)
    prval pfmul1 = mul_add_const {~1} (pfmul)
  in
    loop (pfmul1, pf11, pf2 | p1, n1-1, n2+1, lte)
  end else let
    prval () = array_v_unnil (pf1)
    prval () = mul_elim {0,sizeof(a)} (pfmul)
  in
    (pf2 | ())
  end // end of [if]
//
  val tsz = sizeof<a>
  val tsz = int1_of_size1 (tsz)
  val (pfmul | ofs) = n imul2 tsz
  prval (pf1, pf2) = array_v_split {a} {n,n} (pfmul, pf)
  val (pfres | ()) = loop (pfmul, pf1, pf2 | p+ofs, n, 0, lte)
//
in
  pf := pfres
end // end if [insort]
*)

(* ****** ****** *)

staload "libats/SATS/ilistp.sats"
stadef nil = ilist_nil
stadef cons = ilist_cons

(* ****** ****** *)

staload "libats/SATS/gfarray.sats"

(* ****** ****** *)

typedef lte (a:viewt@ype) =
  {x1,x2:int} (&elt (a, x1), &elt (a, x2)) -> bool (x1 <= x2)
// end of [lte]

(* ****** ****** *)

stadef ORD = ISORD
stadef PERM = PERMUTE
stadef SNOC = SNOC
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
prfun ORD_ins
  {x:int} {y1:int | x <= y1} {ys1:ilist}
  (pf: ORD (cons (y1, ys1))): ORD (cons (x, cons (y1, ys1)))
// end of [ORD_ins]

(* ****** ****** *)

extern
prfun PERM_cons {x:int} {xs1,xs2:ilist}
  (pf: PERM (xs1, xs2)): PERM (cons (x, xs1), cons (x, xs2))

(* ****** ****** *)

extern
prfun SORT_sing {x:int} (): SORT (cons (x, nil), cons (x, nil))

(* ****** ****** *)

extern
prfun SORT_ins
  {x:int} {y1:int | x > y1} {ys1,ys2:ilist}
  (pf1: ORD (cons (y1, ys1)), pf2: SORT (cons (x, ys1), ys2))
  : SORT (cons (x, cons (y1, ys1)), cons (y1, ys2))
// end of [SORT_ins]

(* ****** ****** *)

absprop UNION (xs1:ilist, xs2:ilist, ys:ilist)

extern
prfun UNION_unit1 {xs:ilist} (): UNION (nil, xs, xs)

extern
prfun UNION_snoc_perm
  {xs1x:ilist} {xs1:ilist} {x:int} {xs2:ilist} {ys:ilist} {res:ilist}
  (pf1: SNOC (xs1, x, xs1x), pf2: PERM (cons (x, xs2), ys), pf3: UNION (xs1, ys, res))
  : UNION (xs1x, xs2, res)
// end of [UNION_snoc_perm]

(* ****** ****** *)

fun{a:viewt@ype}
insort {xs:ilist}
  {n:nat} {l:addr} (
  pflen: LENGTH (xs, n)
, pfarr: !gfarray_v (a, xs, l) >> gfarray_v (a, ys, l)
| p: ptr l, n: int n, lte: lte(a)
) : #[ys:ilist] (SORT (xs, ys) | void) = let
//
  fun ins {x:int}
    {ys1:ilist} {n:nat} {l:addr} (
    pfat: elt(a, x)@l
  , pflen: LENGTH (ys1, n)
  , pford: ORD (ys1)
  , pfarr: gfarray_v (a, ys1, l+sizeof(a))
  | p: ptr l, n: int n, lte: lte(a)
  ) : [ys2:ilist] (SORT (cons (x, ys1), ys2), gfarray_v (a, ys2, l) | void) =
  if n > 0 then let
    prval LENGTHcons (pflen1) = pflen
    prval gfarray_v_cons (pfat1, pfarr1) = (pfarr)
    val p1 = p + sizeof<a>
  in
    if !p \lte !p1 then let
      prval pford = ORD_ins {x} (pford)
      prval pfperm = permute_refl ()
      prval pfsrt = ORDPERM2SORT (pford, pfperm)
      prval pfarr = gfarray_v_cons {a} (pfat1, pfarr1)
    in
      (pfsrt, gfarray_v_cons (pfat, pfarr) | ())
    end else let
      val x = !p
      val () = !p := !p1
      val () = !p1 := x
      prval ISORDcons (pford1, _) = pford
      val (pfsrt1, pfarr1res | ()) = ins (pfat1, pflen1, pford1, pfarr1 | p1, n-1, lte)
      prval pfsrt = SORT_ins {x} (pford, pfsrt1)
    in
      (pfsrt, gfarray_v_cons (pfat, pfarr1res) | ())
    end // end of [if]
  end else let
    prval LENGTHnil () = pflen
  in
    (SORT_sing (), gfarray_v_cons (pfat, pfarr) | ())
  end // end of [if]
//
  fun loop {xs1,xs2:ilist}
    {n1,n2:nat} {l:addr} {ofs:int} (
    pf1len: LENGTH (xs1, n1)
  , pf2len: LENGTH (xs2, n2)
  , pf2ord: ORD (xs2)
  , pfmul: MUL (n1, sizeof(a), ofs)
  , pf1arr: gfarray_v (a, xs1, l), pf2arr: gfarray_v (a, xs2, l+ofs)
  | p: ptr (l+ofs), n1: int n1, n2: int n2, lte: lte(a)
  ) : [xs,ys:ilist] (
    UNION (xs1, xs2, ys), ORD (ys), gfarray_v (a, ys, l) | void
  ) = if n1 > 0 then let
    prval (pfsnoc, pf1arr, pf1at) = gfarray_v_unextend {a} (pf1len, pfmul, pf1arr)
    val p1 = p-sizeof<a>
//
    prval pf1len1 = length_istot ()
    prval pf1len_alt = snoc_length_lemma (pfsnoc, pf1len1)
    prval () = length_isfun (pf1len, pf1len_alt)
    prval pf1len = pf1len1
//
    val (pf2srt, pf2arr | ()) = ins (pf1at, pf2len, pf2ord, pf2arr | p1, n2, lte)
    prval pf2ord = SORT2ORD (pf2srt)
    prval pf2perm = SORT2PERM (pf2srt)
    prval pf2len = permute_length_lemma (pf2perm, LENGTHcons (pf2len))
    prval pfmul1 = mul_add_const {~1} (pfmul)
    val (pfuni, pford, pfarr | ()) = loop (
      pf1len, pf2len, pf2ord, pfmul1, pf1arr, pf2arr | p1, n1-1, n2+1, lte
    ) // end of [val]
    prval pfuni = UNION_snoc_perm (pfsnoc, pf2perm, pfuni)
  in
    (pfuni, pford, pfarr | ())
  end else let
    prval LENGTHnil () = pf1len
    prval gfarray_v_nil () = pf1arr
    prval pfuni = UNION_unit1 ()
    prval () = mul_elim {0,sizeof(a)} (pfmul)
  in
    (pfuni, pf2ord, pf2arr | ())
  end // end of [if]
//
  val tsz = sizeof<a>
  val tsz = int1_of_size1 (tsz)
  val (pfmul | ofs) = n imul2 tsz
  prval [xs1:ilist,xs2:ilist]
    (pf1len, pfapp, pf1arr, pf2arr) =
    gfarray_v_split {a} {xs} {n,n} (pflen, pfmul, pfarr)
//
  prval pf2len1 = length_istot ()
  prval pflen_alt = append_length_lemma (pfapp, pf1len, pf2len1)
  prval () = length_isfun (pflen, pflen_alt)
  prval pf2len = pf2len1
  prval LENGTHnil () = pf2len
//
  prval pfapp_alt = append_unit2 ()
  prval ILISTEQ () = append_isfun (pfapp, pfapp_alt)
//
  prval pf2ord = ISORDnil ()
  val (pfuni, pford, pfresarr | ()) = loop {xs,nil}
    (pf1len, pf2len, pf2ord, pfmul, pf1arr, pf2arr | p+ofs, n, 0, lte)
//
extern prfun UNION_nil2_elim
  {xs,ys:ilist} (pf: UNION (xs, nil, ys)): PERM (xs, ys)
//
  prval pfperm = UNION_nil2_elim (pfuni)
  prval pfsrt = ORDPERM2SORT (pford, pfperm)
//
  prval () = pfarr := pfresarr
in
  (pfsrt | ())
end // end if [insort]

(* ****** ****** *)

(* end of [insort_arr.dats] *)
