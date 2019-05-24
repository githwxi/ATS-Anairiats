//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

staload "myheader.sats"

(* ****** ****** *)

(*
// loaded by atsopt:
staload "prelude/SATS/array.sats"
*)
staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"
staload _(*anon*) = "libats/ngc/DATS/slist.dats"

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"
staload _(*anon*) = "libats/ngc/DATS/slist.dats"

(* ****** ****** *)

staload "contrib/linux/basics.sats"
staload "contrib/linux/SATS/utils.sats"

(* ****** ****** *)

staload "scull.sats"

#define i2sz size1_of_int1
macdef viewout_decode = $UN.viewout_decode

(* ****** ****** *)

absview qtm_v (n: int, l:addr)

extern
prfun qtm_v_nil {n:nat} (): qtm_v (n, null)
extern
prfun qtm_v_takeout
  {n:nat} {l:agz} () : ftakeout (qtm_v (n, l), bytes (n) @ l)
// end of [qtm_v]

(* ****** ****** *)

absview qdat_v (m: int, n: int, l:addr)

extern
prfun qdatptr_fold {m,n:nat} {l:addr}
  (pf: qdat_v (m, n, l) | x: !ptr l >> qdatptr (m, n, l)): void
extern
prfun qdatptr_unfold {m,n:nat} {l:addr}
  (x: !qdatptr (m, n, l) >> ptr l): (qdat_v (m, n, l) | void)

extern
prfun qdat_v_nil
  {m,n:nat} (): qdat_v (m, n, null)
extern
prfun qdat_v_unnil
  {m,n:int} (pf: qdat_v (m, n, null)): void

extern
prfun qdat_v_takeout : {m,n:nat} {l:agz}
  ftakeout (qdat_v (m, n, l), array_v (qtmptr (n), m, l))
// end of [qdat_v_takeout]

extern
prfun qdat_v_takeout_all {m,n:nat} {l:agz}
  (pf : qdat_v (m, n, l)): (kfree_v l, array_v (qtmptr (n), m, l))
// end of [qdat_v_takeout_all]

(* ****** ****** *)

(*
fun qdatptr_free
  {m,n:nat} (p: qdatptr (m, n), m: int m): void
// end of [qdatptr_free]
*)

implement
qdatptr_free
  {m,n} (p, m) = let
//
viewtypedef qtmptr = qtmptr (n)
//
extern fun array_ptr_kfree
  {a:viewt@ype}
  {n:int}
  {l:addr} (
  pf_gc: kfree_v l
, pf_arr: array_v (a?, n, l)
| p_arr: ptr l
) :<> void = "mac#atsctrb_linux_array_ptr_kfree"
//
fun free_agz {l:agz} .<>. (
  pf: qdat_v (m, n, l) | p: ptr l, m: int m
) :<> void = let
  prval (pfgc, pfarr) = qdat_v_takeout_all (pf)
  val m = size1_of_int1 (m)
  val () = array_ptr_clear_fun<qtmptr> (!p, m, lam x =<fun> qtmptr_free (x))
in
  array_ptr_kfree {ptr} (pfgc, pfarr | p)
end // end of [free_agz]
//
prval (pf | ()) =
  qdatptr_unfold (p)
val p = p
prval () = ptr_is_gtez (p)
//
in
  if p > null then
    free_agz (pf | p, m)
  else let
    prval () = qdat_v_unnil (pf)
  in
    // nothing
  end (* end of [if] *)
end // end of [qdatptr_free]

(* ****** ****** *)

#include "scull_qsetlst.hats"

(* ****** ****** *)

implement
qsetlst_make
  {m,n} {ln0} (
  ln0, ln_res
) = let
  viewtypedef qset = qset (m, n)
  fun loop {i0,j0:nat} .<i0>. (
    i0: int i0
  , res: qsetlst (m, n, j0)
  , ln_res: &int j0 >> int j
  ) :<> #[j:nat | j <= i0+j0] qsetlst (m, n, j) =
    if i0 > 0 then let
      val (pfopt | p) = slnode_alloc<qset> ()
    in
      if p > null then let
        prval Some_v (pf) = pfopt
        prval (pfat, fpf) = slnode_v_takeout_val {qset?} (pf)
        val () = p->data := qdatptr_make_null {m,n} ()
        prval () = pf := fpf (pfat)
        val res = slist_cons (pf | p, res)
        val () = ln_res := ln_res + 1
      in
        loop (i0-1, res, ln_res)
      end else let
        prval None_v () = pfopt
      in
        res
      end (* end of [if] *)
    end else res
  // end of [loop]
  val () = ln_res := 0
in
  loop (ln0, slist_nil<qset> (), ln_res)
end // end of [qsetlst_make]

implement qsetlst_free
  {m,n} {ln}
  (xs, m) = let
  stadef T = qset (m, n)
  stadef V = unit_v
  var !p_clo = @lam (
    pf: !V | x: &T >> T?
  ) : void =<clo> qdatptr_free (x.data, m)
  prval pfv = unit_v ()
  val () = slist_free_vclo<T> {V} (pfv | xs, !p_clo)
  prval unit_v () = pfv
in
  // nothing
end // end of [qsetlst_free]

(* ****** ****** *)

extern
prfun qtmptr_vtakeout_bytes_read
  {n:nat} {l:addr}
  (p: !qtmptr (n, l)): (
  option_v (viewout (bytes(n) @ l), l > null)
) // end of [qtmptr_vtakeout_bytes_read]

implement
qdatptr_vtakeout_bytes_read
  {m,n}
  (p, i) = let
  val p1 = ptr_of (p)
in
  if p1 > null then let
    prval (pfdat | ()) = qdatptr_unfold (p)
    prval (pfarr, fpfdat) = qdat_v_takeout (pfdat)
    val i = i2sz (i)
    val (pfat, fpfarr | p_i) = array_ptr_takeout<qtmptr(n)> (pfarr | p1, i)
    val pqtm = ptr_of (!p_i)
    prval pfopt = qtmptr_vtakeout_bytes_read (!p_i)
    prval () = pfarr := fpfarr (pfat)
    prval () = pfdat := fpfdat (pfarr)
    prval () = qdatptr_fold (pfdat | p)
  in
    #[.. | (pfopt | pqtm)]
  end else (
    #[.. | (None_v () | null)]
  ) (* end of [if] *)
end // end of [qdatptr_vtakeout_bytes_read]

(* ****** ****** *)

extern
fun qtmptr_vtakeout_bytes_write
  {n:nat} {l:addr} (
  p: &qtmptr (n, l) >> qtmptr (n, l), n: int n, ntry: int
) : #[l:addr] (
  option_v (viewout (bytes(n) @ l), l > null) | ptr l
) // end of [qtmptr_vtakeout_bytes_write]

implement
qtmptr_vtakeout_bytes_write
  {n} {l} (
  r, n, ntry
) = let
  val p = ptr_of (r)
in
  if p > null then
    (qtmptr_vtakeout_bytes_read (r) | p)
  else if ntry > 0 then
    (qtmptr_vtakeout_bytes_read (r) | p)
  else let
    prval () = ptr_is_gtez (p)
    val () = qtmptr_free_null (r)
    val () = r := qtmptr_make (n)
  in
    qtmptr_vtakeout_bytes_write (r, n, ntry+1)
  end (* end of [if] *)
end // end of [qtmptr_vtakeout_bytes_write]

implement
qdatptr_vtakeout_bytes_write
  {m,n}
  (r, m, n, i, ntry) = let
  val p = ptr_of (r)
in
  if p > null then let
    prval (pfdat | ()) = qdatptr_unfold (r)
    prval (pfarr, fpfdat) = qdat_v_takeout (pfdat)
    val i = i2sz (i)
    val (
      pfat, fpfarr | p_i
    ) = array_ptr_takeout<qtmptr(n)> (pfarr | p, i)
    val (pfopt | pqtm) = qtmptr_vtakeout_bytes_write (!p_i, n, 0)
    prval () = pfarr := fpfarr (pfat)
    prval () = pfdat := fpfdat (pfarr)
    prval () = qdatptr_fold (pfdat | r)
  in
    #[ .. | (pfopt | pqtm) ]
  end else if ntry > 0 then
    #[.. | (None_v () | null)]
  else let
    prval () = ptr_is_gtez (p)
    val () = qdatptr_free_null (r)
    val () = r := qdatptr_make {m,n} (m)
  in
    qdatptr_vtakeout_bytes_write (r, m, n, i, ntry+1)
  end // end of [if]
end // end of [qdatptr_vtakeout_bytes_read]

(* ****** ****** *)

(* end of [scull_data.dats] *)
