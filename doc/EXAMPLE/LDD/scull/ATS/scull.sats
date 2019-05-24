//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

%{#
#include "ATS/scull.cats"
%} // end of [%{#]

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"
stadef viewout = $UN.viewout

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"

(* ****** ****** *)

staload "contrib/linux/basics.sats"
staload FS = "contrib/linux/linux/SATS/fs.sats"
stadef file = $FS.file

(* ****** ****** *)
//
// HX:
// n: quantum size; l: location
//
absviewtype
qtmptr (n:int, l:addr) = ptr
viewtypedef qtmptr (n: int) = [l:addr] qtmptr (n, l)

castfn ptr_of_qtmptr
  {n:nat} {l:addr} (x: !qtmptr (n, l)): ptr l
overload  ptr_of with ptr_of_qtmptr

fun qtmptr_make
  {n:nat}
  (n: int n):<> qtmptr (n) = "scull_qtmptr_make"
fun qtmptr_make_null
  {n:nat} ():<> qtmptr (n, null) = "mac#scull_ptr_make_null"

fun qtmptr_free {n:nat}
  (p: qtmptr (n)):<> void = "scull_qtmptr_free"
fun qtmptr_free_null {n:nat}
  (p: qtmptr (n, null)):<> void = "mac#atspre_ptr_free_null"

(* ****** ****** *)
//
// HX:
// m: qset data size; n: quantum size; l: location
//
absviewtype
qdatptr (m: int, n: int, l:addr) = ptr
viewtypedef
qdatptr (m: int, n: int) = [l:addr] qdatptr (m, n, l)

castfn ptr_of_qdatptr
  {m,n:nat} {l:addr} (x: !qdatptr (m, n, l)): ptr l
overload  ptr_of with ptr_of_qdatptr

fun qdatptr_make
  {m,n:nat}
  (m: int m):<> qdatptr (m, n) = "scull_qdatptr_make"
fun qdatptr_make_null
  {m,n:nat} ():<> qdatptr (m, n, null) = "mac#scull_ptr_make_null"

fun qdatptr_free {m,n:nat}
  (p: qdatptr (m, n), m: int m):<> void // implemented in ATS
fun qdatptr_free_null {m, n:nat}
  (p: qdatptr (m, n, null)):<> void = "mac#atspre_ptr_free_null"

(* ****** ****** *)

viewtypedef
qset (m:int, n:int) =
$extype_struct "scull_qset_struct" of {
  data= qdatptr (m, n) // array(m) of arrays(n)
(*
, _rest= undefined_t
*)
} // end of [qset]
viewtypedef qsetlst (m: int, n: int, ln: int) = slist (qset (m, n), ln)

(* ****** ****** *)

fun qsetlst_make
  {m,n:nat} {ln0:nat} (
  ln0: int ln0
, ln_res: &int? >> int ln
) :<> #[ln:nat | ln <= ln0] qsetlst (m, n, ln)

fun qsetlst_free
  {m,n:nat} {ln:nat} (
  xs: qsetlst (m, n, ln), m: int m
) : void // end of [qsetlst_free]

(* ****** ****** *)
//
// HX: m: qset data size; n: quantum size; ln: qsetlst length
//
(*
struct scull_dev {
  int m_qset;               // the current array size
  int n_quantum;            // the current quantum size
//
  struct scull_qset *data;  // pointer to first quantum set
  int ln_qlst;              // the current qsetlst length
//
  unsigned long size;       // amount of data stored here
//
  unsigned int access_key;  // used by sculluid and scullpriv
//
  struct semaphore sem;     // mutual exclusion semaphore
//
  struct cdev cdev;	    // char device structure
//
} ; // end of [scull_dev]
*)
viewtypedef
scull_dev (
  m: int
, n: int
) = $extype_struct "scull_dev_struct" of {
  empty=empty
, m_qset= int (m)
, n_quantum= int (n)
, _rest= undefined_vt
} // end of [scull_dev]
viewtypedef
scull_dev = [m,n:nat] scull_dev (m, n)

viewtypedef
scull_dev_owned (
  m: int
, n: int
, ln: int
, sz: int
) = $extype_struct "scull_dev_struct" of {
  empty=empty
, m_qset= int (m)
, n_quantum= int (n)
, data= qsetlst (m, n, ln)
, ln_qlst= int (ln)
, size= ulint (sz)
, _rest= undefined_vt
} // end of [scull_dev_owned]

(* ****** ****** *)

dataview
scull_dev_acquire_v
  (m: int, n: int, l: addr, int) =
  | {ln:nat} {sz:nat}
    scull_dev_acquire_v_succ (m, n, l, 0) of scull_dev_owned (m, n, ln, sz) @ l
  | {i:neg}
    scull_dev_acquire_v_fail (m, n, l, i) of scull_dev (m, n) @ l
// end of [scull_dev_acquire_v]

fun scull_dev_acquire
  {m,n:int} {ln:int} {sz:int} {l:addr}
  (pf: scull_dev (m, n) @ l | p: ptr l)
  : [i:int] (scull_dev_acquire_v (m, n, l, i) | int i)
  = "mac#scull_dev_acquire"
// end of [scull_dev_acquire]

fun scull_dev_release
  {m,n:int} {ln:int} {sz:int}
  (dev: &scull_dev_owned (m,n,ln,sz) >> scull_dev (m, n)): void
  = "mac#scull_dev_release"
// end of [scull_dev_release]

(* ****** ****** *)

abst@ype loff_t (i:int) = $extype"loff_t"

(* ****** ****** *)

fun scull_trim_main
  {m0,n0:nat}
  {ln:nat}
  {sz:nat}
  {m,n:pos} (
  dev: &scull_dev_owned (m0, n0, ln, sz) >> scull_dev_owned (m, n, 0, 0)
, m: int m
, n: int n
) : void = "scull_trim_main"

(* ****** ****** *)

(*
fun{a:vt0p}
slist_split_at
  {n:int} {i:nat | i < n} {la:addr}
  (pflst: slist_v (a, n, la) | p: ptr la, i: size_t i)
  : [lm:addr] (slseg_v (a, i, la, lm), slist_v (a, n-i, lm) | ptr lm)
// end of [slist_split_at]
*)
fun scull_follow_lessthan
  {m,n:nat}
  {ln0:int}
  {ln:nat | ln < ln0} (
  xs: !slist (qset(m, n), ln0), ln: int (ln)
) : [lm:agz] (
  viewout (qset(m, n) @ lm) | ptr lm
) = "scull_follow_lessthan"

(* ****** ****** *)

fun scull_follow_main
  {m,n:nat} {ln0:nat} {ln:nat} (
  xs: &slist (qset(m, n), ln0) >> slist (qset(m, n), ln1)
, ln0: &int(ln0) >> int (ln1)
, ln: int (ln)
) : #[ln1:int;lm:addr | ln0 <= ln1] (
  option_v (viewout (qset(m, n) @ lm), lm > null) | ptr (lm)
) = "scull_follow_main"
// end of [fun]

(* ****** ****** *)

fun scull_open_main
  (dev: &scull_dev, file: &file): [i:int | i <= 0] int i
  = "scull_open_main"
// end of [fun]

(* ****** ****** *)

fun qdatptr_vtakeout_bytes_read
  {m,n:nat} {l0:addr} (
  p: !qdatptr (m, n, l0), i: natLt m
) : [l:addr] (
  option_v (viewout (bytes(n) @ l), l > null) | ptr l
) = "scull_qdatptr_vtakeout_bytes_read"

fun scull_read_main
  {m,n:nat}
  {ln0:nat}
  {lbf:addr}
  {cnt:nat}
  {tot:nat} (
  pfbuf: !bytes(cnt) @ lbf
| m: int m, n: int n
, xs: !slist (qset(m, n), ln0)
, ln: natLt (ln0), i: natLt (m), j: natLt (n)
, pbf: uptr (lbf)
, cnt: int (cnt)
, fpos: &loff_t(tot) >> loff_t(tot+max(0, cnt1))
) : #[cnt1:int | cnt1 <= cnt] int (cnt1) = "scull_read_main"
// end of [fun]

(* ****** ****** *)

fun qdatptr_vtakeout_bytes_write
  {m,n:nat} {l0:addr} (
  p: &qdatptr (m, n, l0) >> qdatptr (m, n, l0)
, m: int m, n: int n
, i: natLt m
, ntry: int
) : #[l0,l:addr] (
  option_v (viewout (bytes(n) @ l), l > null) | ptr l
) // end of [fun]

fun scull_write_main
  {m,n:nat}
  {ln0,ln:nat}
  {lbf:addr}
  {cnt:nat}
  {tot:nat} (
  pfbuf: !bytes(cnt) @ lbf
| m: int m, n: int n
, xs: &slist (qset(m, n), ln0) >> slist (qset(m, n), ln1)
, ln0: &int (ln0) >> int (ln1)
, ln: int (ln)
, i: natLt (m), j: natLt (n)
, pbf: uptr (lbf)
, cnt: int (cnt)
, fpos: &loff_t(tot) >> loff_t(tot+max(0, cnt1))
) : #[
  ln1,cnt1:int
| ln0 <= ln1
; cnt1 <= cnt
] int (cnt1) = "scull_write_main"
// end of [fun]

(* ****** ****** *)

(* end of [scull.sats] *)
