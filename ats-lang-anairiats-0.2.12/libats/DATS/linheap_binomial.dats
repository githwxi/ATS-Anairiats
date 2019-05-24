(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: November, 2011 *)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading at run-time

(* ****** ****** *)

staload "libats/SATS/linheap_binomial.sats"

(* ****** ****** *)
//
// a specialized version can be implemented on the spot
//
implement{a} compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)
//
(* ****** ****** *)

(*
** binomial trees:
** btree(a, n) is for a binomial tree of rank(n)
*)
dataviewtype
btree (a:viewt@ype+, int(*rank*)) =
  | {n:nat}
    btnode (a, n) of (int (n), a, btreelst (a, n))
// end of [btree]

and
btreelst (a:viewt@ype+, int(*rank*)) =
  | {n:nat}
    btlst_cons (a, n+1) of (btree (a, n), btreelst (a, n))
  | btlst_nil (a, 0)
// end of [btreelst]

(* ****** ****** *)

fun{a:vt0p}
btree_rank
  {n:nat} .<>. (
  bt: !btree (a, n)
) :<> int (n) = let
  val btnode (n, _, _) = bt in fold@ (bt) ; n
end // end of [btree_rank]

fun{a:t@ype}
btreelst_free
  {n:nat} .<n>.
  (bts: btreelst (a, n)):<> void =
  case+ bts of
  | ~btlst_cons (bt, bts) => let
      val ~btnode (_, _, bts1) = bt
    in
      btreelst_free (bts1); btreelst_free (bts)
    end
  |  ~btlst_nil () => ()
// end of [btreelst_free]

(* ****** ****** *)

dataviewtype
bheap (
  a:viewt@ype+, int(*rank*), int(*size*)
) =
  | {n:nat}
    bheap_nil (a, n, 0) of ()
  | {n:nat}{p:int}{sz:nat}{n1:int | n1 > n}
    bheap_cons (a, n, p+sz) of (EXP2 (n, p) | btree (a, n), bheap (a, n1, sz))
// end of [bheap]

(* ****** ****** *)

fun{a:t@ype}
bheap_free
  {n:nat}{sz:nat} .<sz>.
  (hp: bheap (a, n, sz)):<> void =
  case+ hp of
  | ~bheap_cons
      (pf | bt, hp) => let
      prval () = exp2_ispos (pf)
      val ~btnode (_, _, bts) = bt
    in
      btreelst_free (bts); bheap_free (hp)
    end
  | ~bheap_nil () => ()
// end of [bheap_free]

(* ****** ****** *)

fun{a:vt0p}
btree_btree_merge
  {n:nat} .<>. (
  bt1: btree (a, n)
, bt2: btree (a, n)
, cmp: cmp a
) :<> btree (a, n+1) = let
  val btnode (!p_n1, !p_x1, !p_bts1) = bt1
  val btnode (!p_n2, !p_x2, !p_bts2) = bt2
  val sgn = compare_elt_elt<a> (!p_x1, !p_x2, cmp)
in
  if sgn <= 0 then let
    prval () = fold@ (bt2)
    val () = !p_n1 := !p_n1 + 1
    val () = !p_bts1 := btlst_cons (bt2, !p_bts1)
  in
    fold@ (bt1); bt1
  end else let
    prval () = fold@ (bt1)
    val () = !p_n2 := !p_n2 + 1
    val () = !p_bts2 := btlst_cons (bt1, !p_bts2)
  in
    fold@ (bt2); bt2
  end // end of [if]
end // end of [btree_btree_merge]

(* ****** ****** *)

fun{a:vt0p}
btree_bheap_merge
  {sz:nat}{n,n1:nat | n <= n1}{p:int} .<sz>. (
  pf: EXP2 (n, p) | bt: btree (a, n), n: int (n), hp: bheap (a, n1, sz)
, cmp: cmp a
) :<> [n2:int | n2 >= min(n, n1)] bheap (a, n2, sz+p) =
  case+ hp of
  | ~bheap_nil () =>
      bheap_cons (pf | bt, bheap_nil {a} {n+1} ())
    // end of [bheap_nil]
  | bheap_cons (pf1 | !p_bt1, !p_hp1) => let
      val n1 = btree_rank<a> (!p_bt1)
    in
      if n < n1 then let
        prval () = fold@ (hp) in bheap_cons {a} (pf | bt, hp)
      end else if n > n1 then let
        val () = !p_hp1 := btree_bheap_merge<a> (pf | bt, n, !p_hp1, cmp)
        prval () = fold@ (hp) 
      in
        hp
      end else let
        prval () = exp2_ispos (pf1)
        prval () = exp2_isfun (pf, pf1)
        val bt1 = !p_bt1
        val bt = btree_btree_merge (bt, bt1, cmp)
        val hp1 = !p_hp1
        val () = free@ {a}{0}{0}{0}{1} (hp)
      in
        btree_bheap_merge (EXP2ind (pf) | bt, n+1, hp1, cmp)
      end // end of [if]
    end (* end of [bheap_cons] *)
// end of [btree_bheap_merge]

(* ****** ****** *)

fun{a:vt0p}
bheap_bheap_merge
  {n1,n2:nat}
  {sz1,sz2:nat} .<sz1+sz2>. (
  hp1: bheap (a, n1, sz1)
, hp2: bheap (a, n2, sz2)
, cmp: cmp a
) :<> [n:int | n >= min(n1, n2)] bheap (a, n, sz1+sz2) =
  case+ hp1 of
  | ~bheap_nil () => hp2
  | bheap_cons (pf1 | !p_bt1, !p_hp11) => (
    case+ hp2 of
    | ~bheap_nil () => (fold@ (hp1); hp1)
    | bheap_cons (pf2 | !p_bt2, !p_hp21) => let
//
        prval () = exp2_ispos (pf1)
        prval () = exp2_ispos (pf2)
//
        val n1 = btree_rank<a> (!p_bt1)
        and n2 = btree_rank<a> (!p_bt2)
      in
        if n1 < n2 then let
          prval () = fold@ (hp2)
          val () = !p_hp11 := bheap_bheap_merge (!p_hp11, hp2, cmp)
          prval () = fold@ (hp1)
        in
          hp1
        end else if n1 > n2 then let
          prval () = fold@ (hp1)
          val () = !p_hp21 := bheap_bheap_merge (hp1, !p_hp21, cmp)
          prval () = fold@ (hp2)
        in
          hp2
        end else let
          prval () = exp2_isfun (pf1, pf2)
          val bt12 = btree_btree_merge (!p_bt1, !p_bt2, cmp)
          val hp11 = !p_hp11 and hp21 = !p_hp21
          val () = free@ {a}{0}{0}{0}{1} (hp1)
          val () = free@ {a}{0}{0}{0}{1} (hp2)
        in
          btree_bheap_merge (EXP2ind (pf1) | bt12, n1+1, bheap_bheap_merge (hp11, hp21, cmp), cmp)
        end // end of [if]
      end (* end of [bheap_cons] *)
    ) // end of [bheap_cons]
// end of [bheap_bheap_merge]

(* ****** ****** *)

local

staload UN = "prelude/SATS/unsafe.sats"
staload _(*anon*) = "prelude/DATS/unsafe.dats"

in // in of [local]

fun{a:vt0p}
bheap_search_ref
  {n:nat}{sz:pos} .<>. (
  hp0: !bheap (a, n, sz), cmp: cmp a
) :<> ptr = let
//
  fun search
    {n:nat}{sz:nat}{l:addr} .<sz>. (
    hp0: !bheap (a, n, sz), p_x0: ptr l, cmp: cmp a
  ) :<> ptr =
    case+ hp0 of
    | bheap_cons (pf | !p_bt, !p_hp) => let
        prval () = exp2_ispos (pf)
        val btnode (_, !p_x, _) = !p_bt
        prval (pfat, fpf) = __assert () where {
          extern praxi __assert (): (a@l, a@l -<lin,prf> void)
        } // end of [prval]
        val sgn = compare_elt_elt<a> (!p_x0, !p_x, cmp)
        prval () = fpf (pfat)
        prval () = fold@ (!p_bt)
        val res = (
          if sgn > 0 then search (!p_hp, p_x, cmp) else search (!p_hp, p_x0, cmp)
        ) : ptr // end of [val]
        prval () = fold@ (hp0)
      in
        res
      end // end of [bheap_cons]
    | bheap_nil () => let
        prval () = fold@ (hp0) in p_x0
      end // end of [bheap_nil]
  (* end of [search] *)
//
  val+ bheap_cons
    (pf0 | !p_bt0, !p_hp1) = hp0
  val+ btnode (_, !p_x0, _) = !p_bt0
  prval () = fold@ (!p_bt0)
  val res = search (!p_hp1, p_x0, cmp)
  prval () = fold@ (hp0)
in
  res
end // end of [bheap_search_ref]

(* ****** ****** *)

fun{a:vt0p}
bheap_remove
  {n:nat}{sz:pos} .<>. (
  hp0: &bheap (a, n, sz) >> bheap (a, n1, sz-p)
, cmp: cmp a
) :<> #[
  n1,n2,p:int | n1 >= n; n2 >= n; sz >= p
] (
  EXP2 (n2, p) | btree (a, n2)
) = let
//
// HX: [search] and [remove] can be merged into one
//
  fun search
    {n:nat}{sz:nat} .<sz>. (
    hp0: !bheap (a, n, sz), x0: &a, pos: &Nat, cmp: cmp a
  ) :<> void = let
  in
    case+ hp0 of
    | bheap_cons (pf | !p_bt, !p_hp) => let
        prval () = exp2_ispos (pf)
        val+ btnode (_, !p_x, _) = !p_bt
        prval () = __assert (p_x) where {
          extern praxi __assert {l:addr} (p: ptr l): [l > null] void
        } // end of [prval]
        val sgn = compare_elt_elt<a> (x0, !p_x, cmp)
        val () = if sgn > 0 then ($UN.ptrset<a> (&x0, $UN.ptrget<a>(p_x)); pos := pos+1)
        prval () = fold@ (!p_bt)
        val () = search (!p_hp, x0, pos, cmp)
        prval () = fold@ (hp0)
      in
        // nothing
      end // [bheap_cons]
    | bheap_nil () => fold@ (hp0)
  end // end of [search]
//
  val+ bheap_cons
    (pf0 | !p_bt0, !p_hp1) = hp0
  val+ btnode (_, !p_x, _) = !p_bt0
  prval () = __assert (p_x) where {
    extern praxi __assert {l:addr} (p: ptr l): [l > null] void
  } // end of [prval]
  prval () = fold@ {a} (!p_bt0)
  var x0: a = $UN.ptrget<a> (p_x) and pos: Nat = 0
  val () = search (!p_hp1, x0, pos, cmp)
  prval () = __clear (x0) where {
    extern praxi __clear (x: &a >> a?): void
  } // end of [prval]
  prval () = fold@ {a} (hp0)
//
  fun remove
    {n:nat}{sz:nat}
    {pos:nat} .<pos>. (
    hp0: &bheap (a, n, sz) >> bheap (a, n1, sz-p)
  , pos: int (pos)
  , btmin: &btree(a, 0)? >> btree (a, n2)
  ) :<> #[
    n1,n2,p:int | n1 >= n; n2 >= n; sz >= p
  ] (
    EXP2 (n2, p) | void
  ) = let
//
    prval () = __assert () where {
      extern praxi __assert (): [sz > 0] void
    } // end of [prval]
//
    val+ bheap_cons (pf | !p_bt, !p_hp) = hp0
    prval () = exp2_ispos (pf)
  in
    if pos > 0 then let
      val (pfmin | ()) = remove (!p_hp, pos-1, btmin)
      prval () = fold@ (hp0)
    in
      (pfmin | ())
    end else let
      val () = btmin := !p_bt
      val hp = !p_hp
      val () = free@ {a}{0}{0}{0}{1} (hp0)
      val () = hp0 := hp
    in
      (pf | ())
    end // end of [if]
  end (* end of [remove] *)
//
  var btmin: btree (a, 0)?
  val (pf | ()) = remove (hp0, pos, btmin)
//
in
  (pf | btmin)
end // end of [bheap_remove]

end // end of [local]

(* ****** ****** *)

assume
heap_viewt0ype_viewtype
  (a:vt0p) = [n,sz:nat] bheap (a, n, sz)
// end of [heap_viewt0ype_viewtype]

(* ****** ****** *)

implement{}
linheap_make_nil {a} () = bheap_nil {a} {0} ()

(* ****** ****** *)

local

extern
fun pow2 {n:nat} (n: int n)
  : [p:pos] (EXP2 (n, p) | size_t (p)) = "atslib_linheap_binomial_pow2"
// end of [pow2]

%{^
ats_size_type
atslib_linheap_binomial_pow2
  (ats_int_type n) {
  size_t res = 1 ; return (res << n) ;
} // end of [atslib_linheap_binomial_pow2]
%} // end of [%{^]

in // in of [loca]

implement{a}
linheap_size (hp0) = let
//
  fun aux {n:nat}{sz:nat} .<sz>.
    (hp0: !bheap (a, n, sz)): size_t (sz) =
    case+ hp0 of
    | bheap_cons (pf | !p_bt, !p_hp) => let
        val n = btree_rank<a> (!p_bt); val (pf1 | p) = pow2 (n)
        prval () = exp2_isfun (pf, pf1)
        val sz = p + aux (!p_hp)
      in
        fold@ (hp0); sz
      end // end of [bheap_cons]
    | bheap_nil () => (fold@ (hp0); size1_of_int1(0))
  (* end of [aux] *)
//
in
  aux (hp0)
end // end of [linheap_size]

end // end of [local]

(* ****** ****** *)

implement
linheap_is_empty {a} (hp) = (
  case+ hp of
  | bheap_cons (_ | _, _) => (fold@ (hp); false)
  | bheap_nil {a}{n} () => (fold@ {a}{n} (hp); true)
) // end of [linheap_is_empty]

implement
linheap_isnot_empty {a} (hp) = (
  case+ hp of
  | bheap_cons (_ | _, _) => (fold@ (hp); true)
  | bheap_nil {a}{n} () => (fold@ {a}{n} (hp); false)
) // end of [linheap_isnot_empty]

(* ****** ****** *)

implement{a}
linheap_insert
  (hp, x0, cmp) = let
  val bt = btnode (0, x0, btlst_nil ())
in
  hp := btree_bheap_merge (EXP2bas () | bt, 0, hp, cmp)
end // end of [linheap_insert]

(* ****** ****** *)

implement{a}
linheap_getmin
  (hp0, cmp, res) = let
  val p_min =
    linheap_getmin_ref (hp0, cmp)
  // end of [val]
  val [l:addr] p_min = ptr1_of_ptr (p_min)
in
//
if p_min > null then let
  prval (pf, fpf) = __assert () where {
    extern praxi __assert (): (a @ l, a @ l -<lin,prf> void)
  } // end of [prval]
  val () = res := !p_min
  prval () = fpf (pf)
  prval () = opt_some {a} (res) in true
end else let
  prval () = opt_none {a} (res) in false
end // end of [if]
//
end // end of [linheap_getmin]

implement{a}
linheap_getmin_ref (hp0, cmp) = let
(*
val () = (
  print ("linheap_getmin_ref: enter"); print_newline ()
) // end of [val]
*)
in
//
case+ hp0 of
| bheap_cons
    (pf | _, _) => let
    prval () = exp2_ispos (pf); prval () = fold@ (hp0)
  in
    bheap_search_ref (hp0, cmp)
  end // end of [bheap_cons]
| bheap_nil {a}{n} () => (fold@ {a}{n} (hp0); null)
//
end // end of [linheap_getmin_ref]

(* ****** ****** *)

local

staload _(*anon*) = "prelude/DATS/list_vt.dats"

in // in of [local]

implement{a}
linheap_delmin
  (hp, cmp, res) = let
(*
val () = (
  print ("linheap_delmin: enter"); print_newline ()
) // end of [val]
*)
in
//
case+ hp of
| bheap_cons
    (pf0 | _, _) => let
    prval () = exp2_ispos (pf0)
    prval () = fold@ (hp)
    val (_(*pf*) | btmin) = bheap_remove (hp, cmp)
    val ~btnode (_, x, bts) = btmin
    val () = res := x
    prval () = opt_some {a} (res)
    val hp1 = hp1 where {
      fun loop {n:nat}{sz:nat} .<n>. (
        bts: btreelst (a, n), hp: bheap (a, n, sz)
      ) :<> [sz:nat] bheap (a, 0, sz) =
        case+ bts of
        | ~btlst_cons (bt, bts) => let
            prval pf = exp2_istot () in loop (bts, bheap_cons (pf | bt, hp))
          end // end of [btlst_cons]
        | ~btlst_nil () => hp
      // end of [loop]
      val hp1 = loop (bts, bheap_nil)
(*
//
// HX: This unsafe trick seems to gain by 5%
//
      viewtypedef T = btree (a, 0)
      val xs = __cast (bts) where {
        extern castfn __cast {n:nat} (bts: btreelst (a, n)):<> List_vt (T)
      } (* end of [val] *)
      val xs = list_vt_reverse<T> (xs)
      val hp1 = __cast (xs) where {
        extern castfn __cast (xs: List_vt (T)):<> [sz:nat] bheap (a, 0, sz)
      } (* end of [val] *)
*)
    } // end of [val]
    val () = hp := bheap_bheap_merge (hp, hp1, cmp)
  in
    true
  end // end of [bheap_cons]
| bheap_nil {a}{n} () => let
    prval () = opt_none {a} (res) in fold@ {a}{n} (hp); false
  end // end of [bheap_nil]
// end of [case]
//
end // end of [linheap_delmin]

end // end of [local]

(* ****** ****** *)

implement{a}
linheap_merge
  (hp1, hp2, cmp) = bheap_bheap_merge<a> (hp1, hp2, cmp)
// end of [linheap_merge]

(* ****** ****** *)

implement{a}
linheap_free (hp) = bheap_free (hp)

(* ****** ****** *)

implement{a}
linheap_free_vt (hp) = let
  viewtypedef VT = heap (a) in
  case+ hp of
  | bheap_cons
      (pf | _, _) => true where {
      prval () = fold@ (hp); prval () = opt_some {VT} (hp)
    } // end of [B]
  | bheap_nil () => false where {
      prval () = opt_none {VT} (hp)
    } // end of [E]
end // end of [linheap_free_vt]

(* ****** ****** *)

(* end of [linheap_binomail.dats] *)
