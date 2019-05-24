//
// A parallelized implementation of mergesort
//
// Author: Hongwei Xi (* hwxi AT cs DOT bu DOT edu *)
// Time: March 2008
//

(* ****** ****** *)

#if undefined (ARG_QUICKSORT_MT_DATS) #then

absviewt@ype T

extern fun lte_T_T (x: !T, y: !T):<> bool
extern fun compare_T_T (x: !T, y: !T):<> Sgn

overload compare with compare_T_T
overload <= with lte_T_T

#endif // end of [undefined (ARG_QUICKSORT_MT_DATS)]

(* ****** ****** *)

#define ARG_INSORT_DATS 1

(* ****** ****** *)

#include "insort.dats"

(* ****** ****** *)

macdef size = size1_of_int1

(* ****** ****** *)

fn exch {n,i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {A:addr}
  (pf: !array_v (T, n, A) | A: ptr A, i1: int i1, i2: int i2): void = let
  val @(pf1, pf2, fpf | p1, p2) =
    array_ptr_takeout2_tsz {T} (pf | A, (size)i1, (size)i2, sizeof<T>)
  val tmp = !p1; val () = !p1 := !p2; val () = !p2 := tmp
in
  pf := fpf (pf1, pf2)
end // end of [exch]

(* ****** ****** *)

fun innerLoop_l {n,l,r:int | 0 <= l; l <= r+1; r < n} {A:addr} .<n-l>.
  (pf: !array_v (T, n, A) | A: ptr A, pivot: !T, l: int l, r: int r)
  : natLte (r+1) = begin
  if l <= r then let
    val (pf1, fpf | p1) = array_ptr_takeout_tsz {T} (pf | A, (size)l, sizeof<T>)
  in
    if !p1 <= pivot then let
      prval () = pf := fpf (pf1)
    in
      innerLoop_l (pf | A, pivot, l+1, r)
    end else begin
      pf := fpf (pf1); l
    end
  end else begin
    l // return value
  end
end // end of [innerLoop_l]

fun innerLoop_r {n,l,r:int | 0 <= l; l <= r+1; r < n} {A:addr} .<r+1>.
  (pf: !array_v (T, n, A) | A: ptr A, pivot: !T, l: int l, r: int r)
  : intBtw (l-1, n) = begin
  if l <= r then let
    val (pf1, fpf | p1) = array_ptr_takeout_tsz {T} (pf | A, (size)r, sizeof<T>)
  in
    if pivot <= !p1 then let
      prval () = pf := fpf (pf1)
    in
      innerLoop_r (pf | A, pivot, l, r-1)
    end else begin
      pf := fpf (pf1); r
    end
  end else begin
    r // return value
  end
end // end of [innerLoop_r]

fun outerLoop {n,l,r:int | 0 <= l; l <= r+1; r < n} {A:addr}
  (pf: !array_v (T, n, A) | A: ptr A, pivot: !T, l: int l, r: int r)
  : natLte n = let
  val l = innerLoop_l (pf | A, pivot, l, r)
  val r = innerLoop_r (pf | A, pivot, l, r)
in
  if l < r then begin
    exch (pf | A, l, r); outerLoop (pf | A, pivot, l+1, r-1)
  end else begin
    l // the pivot
  end
end // end of [outerLoop]

(* ****** ****** *)

fn partition {n:nat | n >= 2} {A:addr}
  (pf: !array_v (T, n, A) | A: ptr A, n: int n): natLt n = let
  val (pf_mul | ofs) = (size)n szmul2 sizeof<T>
  prval pf1_mul = mul_add_const {~1} (pf_mul)
  prval @(pf1, pf2) = array_v_unextend {T} (pf_mul, pf)
  val pivot = ptr_get_vt<T> (pf2 | A + ofs - sizeof<T>)
  val i_pivot = outerLoop (pf1 | A, pivot, 0, n-2)
  val () =
    if i_pivot < n - 1 then let
      val (pf11, fpf1 | p) = begin
        array_ptr_takeout_tsz {T} (pf1 | A, (size)i_pivot, sizeof<T>)
      end
      val () = ptr_set_vt<T> (pf2 | A + ofs - sizeof<T>, !p)
      val () = !p := pivot; prval () = pf1 := fpf1 (pf11)
    in
      // empty
    end else begin
      ptr_set_vt<T> (pf2 | A + ofs - sizeof<T>, pivot)
    end
  prval () = pf := array_v_extend {T} (pf1_mul, pf1, pf2)
in
  i_pivot
end // end of [partition]

#define THRESHOLD 16

fun qsort_main {n:nat} {A:addr}
  (pf: !array_v (T, n, A) | A: ptr A, n: int n)
  : void = begin
  if n >= THRESHOLD then let
    val i_pivot = partition (pf | A, n)
    val (pf_mul | ofs) = (size)i_pivot szmul2 sizeof<T>
      prval (pf1, pf2) = array_v_split {T} (pf_mul, pf)
    prval (pf21, pf22) = array_v_uncons {T} (pf2)
    prval pf1_mul = mul_add_const {1} (pf_mul)
    val () = qsort_main (pf1 | A, i_pivot)
    and () = qsort_main (pf22 | A+ofs+sizeof<T>, n-i_pivot-1)
    prval () = pf2 := array_v_cons {T} (pf21, pf22)
    prval () = pf := array_v_unsplit {T} (pf_mul, pf1, pf2)
  in
    // empty
  end else begin
    // empty
  end (* end of [if] *)
end // end of [qsort]

fun qsort {n:nat} {A:addr}
  (pf: !array_v (T, n, A) | A: ptr A, n: int n): void = begin
  qsort_main (pf | A, n); insort (pf | A, n)
end // end of [qsort]

(* ****** ****** *)

(* end of [quicksort_mt.dats] *)
