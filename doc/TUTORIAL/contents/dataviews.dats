(*

//
// Author: Hongwei Xi (August, 2007)
//
// Some lemmas for array manipulation
//

*)

dataview array_v (a: viewt@ype+, int, addr) =
  | {l:addr} array_v_none (a, 0, l)
  | {n:nat} {l:addr} array_v_some (a, n+1, l) of (a @ l, array_v (a, n, l+sizeof a))

(* ****** ****** *)

(*
 * array_v_split
 *   {a:viewt@ype} {n,i:nat | i <= n} {l:addr} {off: int} .<i>.
 *   (pf_arr: array_v (a, n, l), pf_mul: MUL (i, sizeof a, off))
 *   : (array_v (a, i, l), array_v (a, n-i, l+off))
 *)

prfun array_v_split
  {a:viewt@ype} {n,i:nat | i <= n} {l:addr} {off: int} .<i>.
  (pf_arr: array_v (a, n, l), pf_mul: MUL (i, sizeof a, off))
  : (array_v (a, i, l), array_v (a, n-i, l+off)) =
  sif i > 0 then let
    prval array_v_some (pf_at, pf_arr) = pf_arr
    prval MULind pf_mul = pf_mul
    prval (pf_arr1, pf_arr2) = array_v_split {a} (pf_arr, pf_mul)
  in
    (array_v_some {a} (pf_at, pf_arr1), pf_arr2)
  end else let
    prval MULbas () = pf_mul
  in
    (array_v_none (), pf_arr)
  end

(*
 * array_v_unsplit
 *   {a:viewt@ype} {n1,n2:nat} {l:addr} {off: int} .<n1>.
 *   (pf_arr1: array_v (a, n1, l),
 *    pf_arr2: array_v (a, n2, l+off),
 *    pf_mul: MUL (n1, sizeof a, off))
 *   : array_v (a, n1+n2, l)
 *)

prfun array_v_unsplit
  {a:viewt@ype} {n1,n2:nat} {l:addr} {off: int} .<n1>.
  (pf_arr1: array_v (a, n1, l), pf_arr2: array_v (a, n2, l+off), pf_mul: MUL (n1, sizeof a, off))
  : array_v (a, n1+n2, l) =
  sif n1 > 0 then let
    prval array_v_some (pf_at, pf_arr1) = pf_arr1
    prval MULind pf_mul = pf_mul
    prval pf_arr = array_v_unsplit {a} (pf_arr1, pf_arr2, pf_mul)
  in
    array_v_some {a} (pf_at, pf_arr)
  end else let
    prval array_v_none () = pf_arr1
    prval MULbas () = pf_mul
  in
    pf_arr2
  end

(* ****** ****** *)

(*
 * array_v_takeout
 *   {n,i:nat | i < n} {l:addr} {off: int}
 *   (pf_arr: array_v (a, n, l), pf_mul: MUL (i, sizeof a, off))
 *   : (a @ (l+off), a @ (l+off) -<lin> array_v (a, n, l))
 *)

prfun array_v_takeout
  {a:viewt@ype} {n,i:nat | i < n} {l:addr} {off: int} .<i>.
  (pf_arr: array_v (a, n, l), pf_mul: MUL (i, sizeof a, off))
  : (a @ (l+off), a @ (l+off) -<lin> array_v (a, n, l)) =
  sif i > 0 then let
    prval array_v_some (pf_at, pf_arr) = pf_arr
    prval MULind pf_mul = pf_mul
    prval (pf_out, pf_rst) = array_v_takeout {a} (pf_arr, pf_mul)
  in
    (pf_out, llam pf_out => array_v_some {a} (pf_at, pf_rst pf_out))
  end else let
    prval MULbas () = pf_mul
    prval array_v_some (pf_at, pf_arr)  = pf_arr
  in
    (pf_at, llam pf_at => array_v_some {a} (pf_at, pf_arr))
  end

(* ****** ****** *)

extern // a template function for read through a pointer
fun{a:t@ype} ptr_get {l:addr} (pf: a @ l | p: ptr l): (a @ l | a)

extern // a template function for write through a pointer
fun{a:t@ype} ptr_set {l:addr} (pf: a @ l | p: ptr l, x: a): (a @ l | void)

fn{a:t@ype} // a template function for array read
  array_ptr_get_at {n,i:nat | i < n} {l:addr}
  (pf_arr: array_v (a, n, l) | p: ptr l, i: size_t i)
  : (array_v (a, n, l) | a) =
  let
    val (pf_mul | off) = mul2_size1_size1 (i, sizeof<a>)
    prval (pf_elt, pf_rst) = array_v_takeout {a} (pf_arr, pf_mul)
    val (pf_elt | x) = ptr_get<a> (pf_elt | p + off)
  in
    (pf_rst pf_elt | x)
  end

fn{a:t@ype} // a template function for array write
  array_ptr_set_at {n,i:nat | i < n} {l:addr}
  (pf_arr: array_v (a, n, l) | p: ptr l, i: size_t i, x: a)
  : (array_v (a, n, l) | void) =
  let
    val (pf_mul | off) = mul2_size1_size1 (i, sizeof<a>)
    prval (pf_elt, pf_rst) = array_v_takeout {a} (pf_arr, pf_mul)
    val (pf_elt | ()) = ptr_set<a> (pf_elt | p + off, x)
  in
    (pf_rst pf_elt | ())
  end

(* ****** ****** *)

(* end of [dataviews.dats] *)
