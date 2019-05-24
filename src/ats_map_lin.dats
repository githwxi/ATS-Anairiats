(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2008
//
(* ****** ****** *)
//
// HX: A linear map implementation based on randomized binary search trees
//
(* ****** ****** *)

%{^
#include <stdlib.h>
%} // end of [%{^]

(* ****** ****** *)

staload "ats_map_lin.sats"

(* ****** ****** *)

dataviewtype
bst (key:t@ype, itm:t@ype+, int) =
  | {nl,nr:nat} BSTcons (key, itm, 1+nl+nr) of
      (int (1+nl+nr), key, itm, bst (key, itm, nl), bst (key, itm, nr))
  | BSTnil (key, itm, 0)
// end of [bst]

(* ****** ****** *)

fun{key,itm:t@ype}
bst_free {n:nat} .<n>.
  (t: bst (key, itm, n)):<> void = begin case+ t of
  | ~BSTcons (_, _, _, tl, tr) => (bst_free tl; bst_free tr)
  | ~BSTnil () => ()
end // end of [bst_free]

(* ****** ****** *)

fn{key,itm:t@ype}
bst_size {n:nat} (t: !bst (key, itm, n)):<> int n = case+ t of
  | BSTcons (n, _, _, _, _) => (fold@ t; n) | BSTnil _ => (fold@ t; 0) 
// end of [bst_size]

fn{key,itm:t@ype}
bst_is_empty {n:nat}
  (t: !bst (key, itm, n)):<> bool (n == 0) =
  case+ t of BSTcons _ => (fold@ t; false) | BSTnil _ => (fold@ t; true)
// end of [bst_is_empty]

(* ****** ****** *)

fun{key,itm:t@ype}
bst_insert_atroot {n:nat} .<n>. (
  t: bst (key, itm, n)
, k0: key
, i0: itm
, cmp: (key, key) -<fun> Sgn
) :<> bst (key, itm, n+1) = begin case+ t of
  | BSTcons (!p_n, k, _(*i*), !p_tl, !p_tr) => begin
      if cmp (k0, k) <= 0 then let
        val tl_new = bst_insert_atroot (!p_tl, k0, i0, cmp)
        val+ BSTcons (!p_nl, kl, _(*il*), !p_tll, !p_tlr) = tl_new
        val n = !p_n; val nll = bst_size !p_tll
      in
        !p_tl := !p_tlr; !p_n := n - nll; fold@ t;
        !p_tlr := t; !p_nl := n + 1; fold@ tl_new; tl_new
      end else let
        val tr_new = bst_insert_atroot (!p_tr, k0, i0, cmp)
        val+ BSTcons (!p_nr, kr, _(*ir*), !p_trl, !p_trr) = tr_new
        val n = !p_n; val nrr = bst_size !p_trr
      in
        !p_tr := !p_trl; !p_n := n - nrr; fold@ t;
        !p_trl := t; !p_nr := n + 1; fold@ tr_new; tr_new
      end // end of [if]
    end (* end of [BSTcons] *)
  | ~BSTnil () => begin
      BSTcons (1, k0, i0, BSTnil (), BSTnil ())
    end (* end of [BSTnil] *)
end (* end of [bst_insert_atroot] *)

(* ****** ****** *)

fun{key,itm:t@ype}
bst_search {n:nat} .<n>. (
  t: !bst (key, itm, n), k0: key, cmp: (key, key) -<fun> Sgn
) :<> Option_vt itm = begin case+ t of
  | BSTcons (_, k, i, !p_tl, !p_tr) => begin case+ cmp (k0, k) of
    | ~1 => let val ans = bst_search (!p_tl, k0, cmp) in fold@ t; ans end
    |  1 => let val ans = bst_search (!p_tr, k0, cmp) in fold@ t; ans end
    |  0 => let val ans = Some_vt i in fold@ t; ans end
    end // end of [BSTcons]
  | BSTnil () => (fold@ t; None_vt ())
end (* end of [bst_search] *)

(* ****** ****** *)

%{^

ats_bool_type
atsopt_map_lin_dice (
  ats_int_type m, ats_int_type n
) {
  double r = drand48 ();
  return ((m+n)*r < m) ? ats_true_bool : ats_false_bool ;
} // end of [atsopt_map_lin_dice]

%} // end of [%{^]

extern
fun dice {m,n:int | m > 0; n > 0}
  (m: int m, n: int n):<> bool = "atsopt_map_lin_dice"
// end of [dice]

(* ****** ****** *)

fun{key,itm:t@ype}
bst_insert_random {n:nat} .<n>. (
  t: bst (key, itm, n)
, k0: key
, i0: itm
, cmp: (key, key) -<fun> Sgn
) :<> bst (key, itm, n+1) = begin case+ t of
  | BSTcons (!p_n, k, _(*i*), !p_tl, !p_tr) =>
    if dice (1, !p_n) then
      (fold@ t; bst_insert_atroot (t, k0, i0, cmp))
    else begin
      if cmp (k0, k) <= 0 then let
        val () = !p_tl := bst_insert_random (!p_tl, k0, i0, cmp) in
        !p_n := !p_n + 1; fold@ t; t
      end else let
        val () = !p_tr := bst_insert_random (!p_tr, k0, i0, cmp) in
        !p_n := !p_n + 1; fold@ t; t
      end // end of [if]
    end (* end of [BSTcons] *)
  | ~BSTnil () => begin
      BSTcons (1, k0, i0, BSTnil (), BSTnil ())
    end (* end of [BSTnil] *)
end (* end of [bst_insert_random] *)

(* ****** ****** *)

fun{key,itm:t@ype}
bst_join_random
  {nl,nr:nat} .<nl+nr>. (
  tl: bst (key, itm, nl)
, tr: bst (key, itm, nr)
) :<> bst (key, itm, nl+nr) = begin case+ tl of
  | BSTcons (!p_nl, kl, il, !p_tll, !p_tlr) => begin case+ tr of
    | BSTcons (!p_nr, kr, ir, !p_trl, !p_trr) => let
        val n = !p_nl + !p_nr
      in
        if dice (!p_nl, !p_nr) then begin
          fold@ tr; !p_tlr := bst_join_random (!p_tlr, tr);
          !p_nl := n; fold@ tl; tl
        end else begin
          fold@ tl; !p_trl := bst_join_random (tl, !p_trl);
          !p_nr := n; fold@ tr; tr
        end // end of [if]
      end (* end of [BSTcons] *)
    | ~BSTnil () => (fold@ tl; tl)
    end // end of [BSTcons]
  | ~BSTnil () => tr
end // end of [bst_join_random]

(* ****** ****** *)
//
// the function [bst_remove_random] can be implemented more elegantly by
// exploiting the existential quantifier #[...] as follows:
// {n:nat} (
//   t: bst (key, itm, n)
// , k0: key
// , r1: &Int? >> int i
// , r2: &Option_vt itm? >> option_vt (itm, i > 0)
// ) : #[i:two | i <= n] bst (key, itm, n-i)
//
fun{key,itm:t@ype}
bst_remove_random
  {n:nat} {l1,l2:addr} .<n>. (
  pf1: Int? @ l1
, pf2: Option_vt (itm)? @ l2
| t: bst (key, itm, n)
, k0: key, p1: ptr l1
, p2: ptr l2
, cmp: (key, key) -<fun> Sgn
) :<> [i:two | i <= n] (
  int i @ l1, option_vt (itm, i > 0) @ l2 | bst (key, itm, n-i)
) = begin
  case+ t of
  | BSTcons {..} {nl,nr}
      (!p_n, k, i, !p_tl, !p_tr) => begin case+ cmp (k0, k) of
    | ~1 => let
        val [i:int] (pf1, pf2 | tl_new) =
          bst_remove_random (pf1, pf2 | !p_tl, k0, p1, p2, cmp)
      in
        !p_n := !p_n - !p1; !p_tl := tl_new; fold@ t; #[i | (pf1, pf2 | t)]
      end // end of [~1]
    |  1 => let
        val [i:int] (pf1, pf2 | tr_new) =
          bst_remove_random (pf1, pf2 | !p_tr, k0, p1, p2, cmp)
      in
        !p_n := !p_n - !p1; !p_tr := tr_new; fold@ t; #[i | (pf1, pf2 | t)]
      end // end of [1]
    |  0 => let
        val t_new = bst_join_random (!p_tl, !p_tr)
      in
        !p1 := 1; !p2 := Some_vt i; free@ {key,itm} {nl,nr} (t);
        #[1 | (pf1, pf2 | t_new)]
      end // end of [0]
    end // end of [BSTcons]
  | BSTnil () => begin
      !p1 := 0; !p2 := None_vt (); fold@ t; #[0 | (pf1, pf2 | t)]
    end // end of [BSTnil]
end // end of [bst_remove_random]

(* ****** ****** *)

fun{key,itm:t@ype}
bst_select
  {n,s:nat | s < n} .<n>. (
  t: !bst (key, itm, n), s: int s
) :<> itm = let 
  val BSTcons (_, k, i, !p_tl, !p_tr) = t
  val nl = bst_size !p_tl
in
  case+ compare (s, nl) of
  | ~1 => let
      val ans = bst_select<key,itm> (!p_tl, s)
    in
      fold@ {key,itm} (t); ans
    end // end of [~1]
  |  1 => let
      val ans = bst_select<key,itm> (!p_tr, s-nl-1)
    in
      fold@ {key,itm} (t); ans
    end // end of [ 1]
  |  _ (* 0 *) => (fold@ {key,itm} (t); i)
end // end of [bst_select]

(* ****** ****** *)
//
// infix order listing
//
fn{key,itm:t@ype}
bst_list_inf {n:nat} (
  t: !bst (key, itm, n)
) :<> list_vt (@(key, itm), n) = let
  typedef ki = @(key, itm)
  fun aux {i,j:nat} .<i>. (
      t: !bst (key, itm, i), res: list_vt (ki, j)
    ) :<> list_vt (ki, i+j) = begin case+ t of
    | BSTcons (_, k, i, !p_tl, !p_tr) => let
        val ki = (k, i)
        val res = aux (!p_tl, list_vt_cons (ki, aux (!p_tr, res)))
      in
        fold@ t; res
      end // end of [BSTcons]
    | BSTnil () => (fold@ t; res)
  end // end of [aux]
in
  aux (t, list_vt_nil ())
end // end of [bst_list_inf]

(* ****** ****** *)
//
// infix order foreach
//
fun{key,itm:t@ype}
bst_foreach_inf
  {v:view} {vt:viewtype}
  {n:nat} {f:eff} .<n>. (
  pf: !v
| t: !bst (key, itm, n)
, f: (!v | key, itm, !vt) -<f> void
, env: !vt
) :<f> void = begin case+ t of
  | BSTcons (_, k, i, !p_tl, !p_tr) => let
      val () = bst_foreach_inf (pf | !p_tl, f, env)
      val () = f (pf | k, i, env)
      val () = bst_foreach_inf (pf | !p_tr, f, env)
    in
      fold@ t
    end // end of [BSTcons]
  | BSTnil () => fold@ t
end // end of [bst_foreach_inf]

(* ****** ****** *)

dataviewtype
map (key:t@ype, itm:t@ype+) =
  {n:nat} MAP (key, itm) of ((key, key) -<fun> Sgn, bst (key, itm, n))
assume map_vt = map

(* ****** ****** *)

implement
map_make (cmp) = MAP (cmp, BSTnil ())

implement{key,item}
map_free (m) =
  let val+ ~MAP (cmp, bst) = m in bst_free bst end
// end of [map_free]

implement{key,item}
map_cleanup (m) = let
  val+ MAP (cmp, !p_bst) = m in
  bst_free !p_bst; !p_bst := BSTnil (); fold@ m
end // end of [map_cleanup]
  
(* ****** ****** *)

implement{key,itm}
map_search (m, k) = let
  val+ MAP (cmp, !p_bst) = m
  val ans = bst_search<key,itm> (!p_bst, k, cmp)
in
  fold@ m; ans
end // end of [map_search]

implement{key,itm}
map_insert (m, k, i) = let
  val+ MAP (cmp, !p_bst) = m in
  !p_bst := bst_insert_random<key,itm> (!p_bst, k, i, cmp); fold@ m
end // end of [map_insert]

implement{key,itm}
map_remove (m, k) = let
  val+ MAP (cmp, !p_bst) = m
  var status: int and itmopt: Option_vt itm
  val (pf1, pf2 | bst_new) = bst_remove_random<key,itm>
    (view@ status, view@ itmopt | !p_bst, k, &status, &itmopt, cmp)
  // end of [val]
  prval () = view@ status := pf1 and () = view@ itmopt := pf2
in
  !p_bst := bst_new; fold@ m; itmopt
end // end of [map_remove]

(* ****** ****** *)

implement{key,itm}
map_join (m1, m2) = let
  typedef cmp_t = (key, key) -<fun> Sgn
  fun aux {m:nat} {n:nat} .<n>.
    (t0: bst (key, itm, m), t: bst (key, itm, n), cmp: cmp_t)
    :<> [m:nat] bst (key, itm, m) =
    case+ t of // it is done in infix order
    | ~BSTcons (_, k, i, tl, tr) => t0 where {
         val t0 = aux (t0, tl, cmp)
         var status: int and itmopt: Option_vt itm
         val (pf1, pf2 | t0) = bst_remove_random<key,itm>
           (view@ status, view@ itmopt | t0, k, &status, &itmopt, cmp)
         prval () = view@ status := pf1 and () = view@ itmopt := pf2
         val () = case+ itmopt of ~Some_vt _ => () | ~None_vt () => ()
         val t0 = bst_insert_random (t0, k, i, cmp)
         val t0 = aux (t0, tr, cmp)
       } // end of [list_vt_cons]
    | ~BSTnil () => t0
  // end of [aux]
  val+ MAP (cmp, !p_t1) = m1; val+ ~MAP (_(*cmp*), t2) = m2
in
  !p_t1 := aux (!p_t1, t2, cmp); fold@ m1; m1
end // end of [map_join]

(* ****** ****** *)

implement{key,itm}
map_list_inf (m) = let
  val+ MAP (_(*cmp*), !p_bst) = m
  val ans = bst_list_inf<key,itm> (!p_bst)
in
  fold@ (m); ans
end // end of [map_list_inf]

(* ****** ****** *)

implement{key,itm}
map_foreach_inf (pf | m, f, env) = let
  val+ MAP (_(*cmp*), !p_bst) = m
  val ans = bst_foreach_inf<key,itm> (pf | !p_bst, f, env)
in
  fold@ (m); ans
end // end of [map_foreach_inf]

(* ****** ****** *)

(* end of [ats_map_lin.dats] *)
