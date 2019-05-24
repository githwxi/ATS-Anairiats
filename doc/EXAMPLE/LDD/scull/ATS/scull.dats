//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

staload "myheader.sats"

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"
staload _(*anon*) = "libats/ngc/DATS/slist.dats"

(* ****** ****** *)

staload "contrib/linux/basics.sats"
staload "contrib/linux/SATS/utils.sats"

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"
macdef viewout_decode = $UN.viewout_decode

(* ****** ****** *)

staload
ERRNO = "contrib/linux/linux/SATS/errno.sats"
macdef e2i = $ERRNO.int_of_errno
macdef EFAULT = $ERRNO.EFAULT
macdef ENOMEM = $ERRNO.ENOMEM
macdef ERESTARTSYS = $ERRNO.ERESTARTSYS

(* ****** ****** *)

staload
UACC = "contrib/linux/asm/SATS/uaccess.sats"
macdef clear_user = $UACC.clear_user
macdef copy_to_user = $UACC.copy_to_user
macdef copy_from_user = $UACC.copy_from_user

(* ****** ****** *)

staload
FCNTL = "contrib/linux/linux/SATS/fcntl.sats"
macdef O_ACCMODE = $FCNTL.O_ACCMODE
macdef O_WRONLY = $FCNTL.O_WRONLY

(* ****** ****** *)

staload "scull.sats"

(* ****** ****** *)

#include "scull_qsetlst.hats"

(* ****** ****** *)

extern castfn p2p {l:addr} (p: !ptr l):<> ptr l

(* ****** ****** *)

implement
scull_trim_main
  (dev, m, n) = let
  val m0 = dev.m_qset
  val () = qsetlst_free (dev.data, m0)
  val () = dev.m_qset := m
  val () = dev.n_quantum := n
  val () = dev.data := slist_nil ()
  val () = dev.ln_qlst := 0
  val () = dev.size := 0UL
in
  // nothing
end // end of [scull_trim_main]

(* ****** ****** *)

implement
scull_follow_lessthan
  {m,n}
  {ln0}
  {ln} (
  xs, ln
) : [lm:agz] (
  viewout (qset(m, n) @ lm) | ptr lm
) = (pfout | pm) where {
  viewtypedef qset = qset (m, n)
  prval (pflst | ()) = slist_unfold {qset} (xs)
  val p_xs = p2p (xs)
  val ln = size1_of_int1 (ln)
  val [lm:addr] (pf1, pf2 | pm) =
    slist_split_at<qset> (pflst | p_xs, ln)
//
  prval slseg_v_cons (pf21, pf22) = pf2
  prval (pfat, fpf21) = slnode_v_takeout_val {qset} (pf21)
  prval pfout = $UN.vtakeout {qset @ lm} (pfat)
  prval () = pf21 := fpf21 (pfat)
  prval pf2 = slseg_v_cons (pf21, pf22)
//
  prval () = slist_fold {qset} (slseg_v_append (pf1, pf2) | xs)
} // end of [scull_follow_lessthan]

implement
scull_follow_main
  {m,n} {ln0} {ln}
  (xs, ln0, ln) = let
  viewtypedef qset = qset (m, n)
in
  if ln < ln0 then let
    val (pfout | pm) =
      scull_follow_lessthan (xs, ln)
    // end of [val]
  in
    (Some_v (pfout) | pm)
  end else let
    val df = ln-ln0
    var ln0_add: int?
    val xs_add = qsetlst_make (df+1, ln0_add)
    val () = ln0 := ln0 + ln0_add
  in
    if ln0_add > df then let
      val (pfout | pm) =
        scull_follow_lessthan (xs_add, df)
      // end of [val]
      val () = xs := slist_append<qset> (xs, xs_add)
    in
      (Some_v (pfout) | pm)
    end else let
      val () = xs := slist_append<qset> (xs, xs_add)
    in
      (None_v () | null) // out-of-memory
    end // end of [if]
  end // end of [if]
end // end of [scull_follow_main]

(* ****** ****** *)

extern
fun add_loff_int {i,j:int}
  (x: loff_t i, y: int j): loff_t (i+j) = "mac#add_loff_int"
// end of [fun]

(* ****** ****** *)

implement
scull_read_main
  {m,n}
  {ln0}
  {lb}
  {cnt}
  {tot} (
  pfbuf
| m, n, xs, ln, i, j, pbf, cnt, fpos
) = let
  stadef qset = qset (m, n)
  val [lm:addr] (pfout | pm) = scull_follow_lessthan {m,n} (xs, ln)
  prval (pfqs, fpfqs) = viewout_decode {qset@lm} (pfout)
  val (pfopt | pqtm) = qdatptr_vtakeout_bytes_read (pm->data, i)
  prval () = fpfqs (pfqs)
  stavar cnt: int
  val cnt = imin (cnt, n-j): int (cnt)
  val cnt_ul = $UN.cast {ulint(cnt)} (cnt)
  val nleft = (if pqtm > null then let
    prval Some_v pfout = pfopt
    prval (pf, fpf) = viewout_decode (pfout)
    stavar j: int
    val j = j : int j
    prval (pf1, pf2) = bytes_v_split {n} {j} (pf)
(*
    prval () = verify_constraint {n-j > 0} ()
*)
    val nleft = copy_to_user (pfbuf | pbf, !(pqtm+j), cnt_ul)
    prval () = fpf (bytes_v_unsplit (pf1, pf2))
  in
    nleft
  end else let
    prval None_v () = pfopt
    val nleft = clear_user (pfbuf | pbf, cnt_ul) // pack the buf with 0's
  in
    nleft
  end) : ulint // end of [if]
in  
  if nleft = 0UL then let
    val () = fpos := add_loff_int (fpos, cnt) in cnt
  end else let
    val x = (e2i)EFAULT in ~x
  end // end of [if]
end // end of [scull_read_main]
  
(* ****** ****** *)

implement
scull_write_main
  {m,n}
  {ln0,ln}
  {lbf}
  {cnt}
  {tot} (
  pfbuf
| m, n, xs, ln0, ln, i, j, pbf, cnt, fpos
) = let
  val (pfopt | pm) = scull_follow_main (xs, ln0, ln)
  stavar ln1: int
  val ln1 = ln0: int (ln1)
in
//
if pm > null then let
  prval Some_v pfout = pfopt
  prval (pf, fpf) = viewout_decode (pfout)
  val (pfopt | pqtm) = qdatptr_vtakeout_bytes_write (pm->data, m, n, i, 0)
  prval () = fpf (pf)
in
  if pqtm > null then let  
    prval Some_v pfout = pfopt
    prval (pf, fpf) = viewout_decode (pfout)
    stavar j: int
    val j = j : int j
    prval (pf1, pf2) = bytes_v_split {n} {j} (pf)
    stavar cnt: int
    val cnt = imin (cnt, n-j): int (cnt)
(*
    prval () = verify_constraint {n-j > 0} ()
*)
    val cnt_ul = $UN.cast {ulint(cnt)} (cnt)
    val nleft = copy_from_user (pfbuf | !(pqtm+j), pbf, cnt_ul)
    prval () = fpf (bytes_v_unsplit (pf1, pf2))
  in
    if nleft = 0UL then let
      val () = fpos := add_loff_int (fpos, cnt) in cnt
    end else
      ~(e2i)EFAULT // I/O fault
    // end of [if]
  end else let
    prval None_v () = pfopt in ~(e2i)ENOMEM // out-of-memory
  end (* end of [if] *)
end else let
  prval None_v () = pfopt in ~(e2i)ENOMEM // out-of-memory
end (* end of [if] *)
//
end // end of [scull_write_main]
  
(* ****** ****** *)

extern
fun scull_qset_get
  (): [m:pos] int m = "mac#scull_qset_get"
// end of [fun]
extern
fun scull_quantum_get
  (): [n:pos] int n = "mac#scull_quantum_get"
// end of [fun]

(* ****** ****** *)

implement
scull_open_main
  (dev, file) = let
  val iswronly =
    (file.f_flags land O_ACCMODE) = O_WRONLY
  // end of [val]
in
  if iswronly then let
    val p_dev = &dev
    prval pf_dev = view@ (dev)
    val (pf_dev | i) = scull_dev_acquire (pf_dev | &dev)
  in
    if i >= 0 then let
      prval scull_dev_acquire_v_succ (pf_dev) = pf_dev
      val m = scull_qset_get () and n = scull_quantum_get ()
      val () = scull_trim_main (dev, m, n)
      val () = scull_dev_release (dev)
      prval () = view@ (dev) := pf_dev
    in
      0 (* normal *)
    end else let
      prval scull_dev_acquire_v_fail (pf_dev) = pf_dev
      prval () = view@ (dev) := pf_dev
    in
      ~(e2i)ERESTARTSYS
    end // end of [if]
  end else
    0 (* nothing is done in this case *)
  // end of [if]
end // end of [scull_open_main]

(* ****** ****** *)

(* end of [scull.dats] *)
