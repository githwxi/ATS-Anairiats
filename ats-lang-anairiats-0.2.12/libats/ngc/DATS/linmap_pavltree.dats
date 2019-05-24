(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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

(*
**
** A map implementation based on AVL trees with parent pointers
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by
**   Artyom Shalkhakov (artyom DOT shalkhakov AT gmail DOT com)
** Time: January, 2012 // based on a version done by HX in August, 2009
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time
#define ATS_DYNLOADFLAG 0 // no dynamic loading at run-time

(* ****** ****** *)

staload "libats/ngc/SATS/linmap_pavltree.sats"

(* ****** ****** *)
//
// a specialized version can be implemented on the spot
//
implement{key}
compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

viewdef pavlnode0_v (key:t0p, itm:vt0p, slf:addr) =
  [h:int;lft,rgt,pnt:addr] pavlnode_v (key, itm, h, lft, rgt, pnt, slf)
// end of [pavlnode0_v]

(* ****** ****** *)

dataview
pavltree_v (
  key:t@ype
, itm:viewt@ype+
, int(*height*)
, addr(*parent*)
, addr(*self*)
) =
  | {ll,lr,lp:addr}
    {hl,hr:nat | hl <= hr+1; hr <= hl+1}
    {h:int | h == 1+max(hl,hr)}
    {slf:agz}
    B (key, itm, h, lp, slf) of (
      pavlnode_v (key, itm, h, ll, lr, lp, slf)
    , pavltree_v (key, itm, hl, slf, ll)
    , pavltree_v (key, itm, hr, slf, lr)
    ) // end of [B]
  | {lp:addr} E (key, itm, 0, lp, null)
// end of [dataview pavltree_v]

viewdef
pavltree_v_inc (key:t@ype, itm:viewt@ype, h:int, p:addr, l:addr) =
  [h1:nat | h <= h1; h1 <= h+1] pavltree_v (key, itm, h1, p, l)
// end of [pavltree_v_inc]

viewdef
pavltree_v_dec (key:t@ype, itm:viewt@ype, h:int, p:addr, l:addr) =
  [h1:nat | h1 <= h; h <= h1+1] pavltree_v (key, itm, h1, p, l)
// end of [pavltree_v_dec]

(* ****** ****** *)

fn{key:t0p;itm:vt0p}
  pavltree_height_get {h:nat} {pnt,slf:addr}
  (pf: !pavltree_v (key, itm, h, pnt, slf) | p: ptr slf):<> int h =
  if p > null then let
    prval B (pf_at, pf_tl, pf_tr) = pf
    val h = pavlnode_get_height (pf_at | p)
    prval () = pf := B (pf_at, pf_tl, pf_tr)
  in
    h
  end else let
    prval E () = pf; prval () = pf := E {key,itm} {pnt} ()
  in
    0
  end // end of [if]
// end of [pavltree_height_get]

(* ****** ****** *)

fn{key:t0p;itm:vt0p}
  pavltree_parent_set {h:nat} {pnt0,slf,pnt1:addr} (
    pf: !pavltree_v (key, itm, h, pnt0, slf) >> pavltree_v (key, itm, h, pnt1, slf)
  | p: ptr slf, pp1: ptr pnt1
  ) :<> void =
  if p > null then let
    prval B (pf_at, pf_tl, pf_tr) = pf
    val () = pavlnode_set_parent (pf_at | p, pp1)
    prval () = pf := B (pf_at, pf_tl, pf_tr)
  in
    // nothing
  end else let
    prval E () = pf; prval () = pf := E {key,itm} {pnt1} ()
  in
    // nothing
  end // end of [if]
// end of [pavltree_parent_set]

(* ****** ****** *)

(*
** left rotation for restoring height invariant
*)
fn{key:t0p;itm:vt0p}
  pavltree_lrotate {h:int} {hl,hr:nat | hl+2 == hr} {slf:agz;lft,rgh,pnt:addr} (
    pf_at: pavlnode_v (key, itm, h, lft, rgh, pnt, slf)
  , pf_tl: pavltree_v (key, itm, hl, slf, lft)
  , pf_tr: pavltree_v (key, itm, hr, slf, rgh)
  | p: ptr slf
  ) :<> [slf:agz] (pavltree_v_inc (key, itm, hr, pnt, slf) | ptr slf) = let
  val pp = pavlnode_get_parent<key,itm> (pf_at | p)
  and pl = pavlnode_get_left<key,itm> (pf_at | p)
  and pr = pavlnode_get_right<key,itm> (pf_at | p)
  prval B (pfr_at, pf_trl, pf_trr) = pf_tr
  val prl = pavlnode_get_left<key,itm> (pfr_at | pr)
  and prr = pavlnode_get_right<key,itm> (pfr_at | pr)
  val hrl = pavltree_height_get<key,itm> (pf_trl | prl)
  and hrr = pavltree_height_get<key,itm> (pf_trr | prr)
in
  if hrl <= hrr then begin
    pavlnode_set_height<key,itm> (pfr_at | pr, hrl+2);
    pavlnode_set_parent<key,itm> (pfr_at | pr, pp);
    pavlnode_set_left<key,itm> (pfr_at | pr, p);
    pavlnode_set_height<key,itm> (pf_at | p, hrl+1);
    pavlnode_set_parent<key,itm> (pf_at | p, pr);
    pavlnode_set_right<key,itm> (pf_at | p, prl);
    pavltree_parent_set<key,itm> (pf_trl | prl, p);
    (B {key,itm} (pfr_at, B {key,itm} (pf_at, pf_tl, pf_trl), pf_trr) | pr)
  end else let // [hrl > hrr]: deep rotation
    val hr = pavlnode_get_height<key,itm> (pfr_at | pr)
    prval B (pfrl_at, pf_trll, pf_trlr) = pf_trl
    val prll = pavlnode_get_left<key,itm> (pfrl_at | prl)
    and prlr = pavlnode_get_right<key,itm> (pfrl_at | prl)
  in
    pavlnode_set_height<key,itm> (pfrl_at | prl, hr);
    pavlnode_set_parent<key,itm> (pfrl_at | prl, pp);
    pavlnode_set_left<key,itm> (pfrl_at | prl, p);
    pavlnode_set_right<key,itm> (pfrl_at | prl, pr);
    pavlnode_set_height<key,itm> (pf_at | p, hrl);
    pavlnode_set_parent<key,itm> (pf_at |  p, prl);
    pavlnode_set_right<key,itm> (pf_at | p,  prll);
    pavlnode_set_height<key,itm> (pfr_at | pr, hrl);
    pavlnode_set_parent<key,itm> (pfr_at | pr, prl);
    pavlnode_set_left<key,itm> (pfr_at | pr, prlr);
    pavltree_parent_set<key,itm> (pf_trll | prll, p);
    pavltree_parent_set<key,itm> (pf_trlr | prlr, pr);
    (B {key,itm} (pfrl_at, B {key,itm} (pf_at, pf_tl, pf_trll), B {key,itm} (pfr_at, pf_trlr, pf_trr)) | prl)
  end // end of [if]
end // end of [avltree_lrotate]

(* ****** ****** *)

(*
** right rotation for restoring height invariant
*)
fn{key:t0p;itm:vt0p}
  pavltree_rrotate {h:int} {hl,hr:nat | hl == hr+2} {slf:agz;lft,rgh,pnt:addr} (
    pf_at: pavlnode_v (key, itm, h, lft, rgh, pnt, slf)
  , pf_tl: pavltree_v (key, itm, hl, slf, lft)
  , pf_tr: pavltree_v (key, itm, hr, slf, rgh)
  | p: ptr slf
  ) :<> [slf:agz] (pavltree_v_inc (key, itm, hl, pnt, slf) | ptr slf) = let
  val pp = pavlnode_get_parent<key,itm> (pf_at | p)
  and pl = pavlnode_get_left<key,itm> (pf_at | p)
  and pr = pavlnode_get_right<key,itm> (pf_at | p)
  prval B (pfl_at, pf_tll, pf_tlr) = pf_tl
  val pll = pavlnode_get_left<key,itm> (pfl_at | pl)
  and plr = pavlnode_get_right<key,itm> (pfl_at | pl)
  val hll = pavltree_height_get<key,itm> (pf_tll | pll)
  and hlr = pavltree_height_get<key,itm> (pf_tlr | plr)
in
  if hll >= hlr then begin
    pavlnode_set_height<key,itm> (pfl_at | pl, hlr+2);
    pavlnode_set_parent<key,itm> (pfl_at | pl, pp);
    pavlnode_set_right<key,itm> (pfl_at | pl, p);
    pavlnode_set_height<key,itm> (pf_at | p, hlr+1);
    pavlnode_set_parent<key,itm> (pf_at | p, pl);
    pavlnode_set_left<key,itm> (pf_at | p, plr);
    pavltree_parent_set<key,itm> (pf_tlr | plr, p);
    (B {key,itm} (pfl_at, pf_tll, B {key,itm} (pf_at, pf_tlr, pf_tr)) | pl)
  end else let // [hll < hlr]: deep rotation
    val hl = pavlnode_get_height<key,itm> (pfl_at | pl)
    prval B (pflr_at, pf_tlrl, pf_tlrr) = pf_tlr
    val plrl = pavlnode_get_left<key,itm> (pflr_at | plr)
    and plrr = pavlnode_get_right<key,itm> (pflr_at | plr)
  in
    pavlnode_set_height<key,itm> (pflr_at | plr, hl);
    pavlnode_set_parent<key,itm> (pflr_at | plr, pp);
    pavlnode_set_left<key,itm> (pflr_at | plr, pl);
    pavlnode_set_right<key,itm> (pflr_at | plr, p);
    pavlnode_set_height<key,itm> (pfl_at | pl, hlr);
    pavlnode_set_parent<key,itm> (pfl_at | pl, plr);
    pavlnode_set_right<key,itm> (pfl_at | pl, plrl);
    pavlnode_set_height<key,itm> (pf_at | p, hlr);
    pavlnode_set_parent<key,itm> (pf_at | p, plr);
    pavlnode_set_left<key,itm> (pf_at | p, plrr);
    pavltree_parent_set<key,itm> (pf_tlrl | plrl, pl);
    pavltree_parent_set<key,itm> (pf_tlrr | plrr, p);
    (B {key,itm} (pflr_at, B {key,itm} (pfl_at, pf_tll, pf_tlrl), B {key,itm} (pf_at, pf_tlrr, pf_tr)) | plr)
  end // end of [if]
end // end of [pavlnode_rrotate]

(* ****** ****** *)

dataview pavldiff_v (
  key:t@ype
, itm:viewt@ype+
, (*height*)int
, (*missing subtree height*)int
, (*child: root of the missing pavltree*)addr
, (*direction: left(0) or right(1)*)int
, (*root*)addr
, (*root parent*)addr
, (*self*)addr
) = (* view for a pavltree minus a sub pavltree *)
  | {n,h:nat | h <= n}
    {hl,hr:nat | hl <= hr+1; hr <= hl+1; h==max(hl,hr)+1}
    {lft,rgh,pnt:addr} {dir:two} {rt,rtp:addr}
    {slf:agz}
    B1L (key, itm, n, hl, lft, 0, rt, rtp, slf) of (
      pavlnode_v (key, itm, h, lft, rgh, pnt, slf)
    , pavldiff_v (key, itm, n, h, slf, dir, rt, rtp, pnt)
    , pavltree_v (key, itm, hr, slf, rgh)
    ) // end of [B1L]
  | {n,h:nat | h <= n}
    {hl,hr:nat | hl <= hr+1; hr <= hl+1; h==max(hl,hr)+1}
    {lft,rgh,pnt:addr} {dir:two} {rt,rtp:addr}
    {slf:agz}
    B1R (key, itm, n, hr, rgh, 1, rt, rtp, slf) of (
      pavlnode_v (key, itm, h, lft, rgh, pnt, slf)
    , pavltree_v (key, itm, hl, slf, lft)
    , pavldiff_v (key, itm, n, h, slf, dir, rt, rtp, pnt)
    ) // end of [B1R]
  | {h:nat} {chld:addr} {dir:two} {slf:addr}
    E1 (key, itm, h, h, chld, dir, chld, slf, slf) of ()
// end of [pavldiff_v]

(* ****** ****** *)

prfun pavldiff_pavltree_join
  {key:t0p;itm:vt0p}
  {n,h:nat | h <= n} {chld:addr} {dir:two} {rt,rtp,slf:addr} .<n-h>. (
    fpf: pavldiff_v (key, itm, n, h, chld, dir, rt, rtp, slf)
  , pf0: pavltree_v (key, itm, h, slf, chld)
  ) :<> pavltree_v (key, itm, n, rtp, rt) =
  case+ fpf of
  | B1L (pf_at, fpfl, pfr) => pavldiff_pavltree_join (fpfl, B (pf_at, pf0, pfr))
  | B1R (pf_at, pfl, fpfr) => pavldiff_pavltree_join (fpfr, B (pf_at, pfl, pf0))
  | E1 () => pf0
// end of [pavldiff_pavltree_join]

(* ****** ****** *)

prfn pavldiff_takeout
  {key:t0p;itm:vt0p}
  {n,h:int} {chld:addr} {dir:int} {rt,rtp:addr}
  {slf:addr | slf <> rtp} (
    fpf: pavldiff_v (key, itm, n, h, chld, dir, rt, rtp, slf)
  ) :<> [h0:int;lft,rgh,pnt:addr] (
    pavlnode_v (key, itm, h0, lft, rgh, pnt, slf)
  , pavlnode_v (key, itm, h0, lft, rgh, pnt, slf)
      -<lin> pavldiff_v (key, itm, n, h, chld, dir, rt, rtp, slf)
  ) = case+ fpf of
  | B1L {..} {_,h0} {..} {lft,rgh,pnt} {..} {rt,rtp} (pf_at, fpfl, pfr) =>
      #[h0,lft,rgh,pnt | (pf_at, llam (pf_at) => B1L (pf_at, fpfl, pfr))]
    // end of [B1L]
  | B1R {..} {_,h0} {..} {lft,rgh,pnt} {..} {rt,rtp} (pf_at, pfl, fpfr) =>
      #[h0,lft,rgh,pnt | (pf_at, llam (pf_at) => B1R (pf_at, pfl, fpfr))]
    // end of [B1R]
// end of [pavldiff_takeout]

(* ****** ****** *)

fn{key:t0p;itm:vt0p}
  pavldiff_dir_get
  {n,h:int} {chld:addr | chld > null} {dir:int} {rt:addr}
  {slf:addr} (
    fpf: !pavldiff_v (key, itm, n, h, chld, dir, rt, null, slf) | p: ptr slf, pc: ptr chld
  ) :<> int dir = let
  val dir = if p > null then let
    prval (pf_at, ffpf) = pavldiff_takeout (fpf)
    val dir = (if pc = pavlnode_get_left<key,itm> (pf_at | p) then 0(*left*) else 1(*right*)): int
    prval () = fpf := ffpf (pf_at)
  in
    dir
  end else begin
    0 // it is arbitrarily chosen (from {0,1})
  end : int
in
  __cast (dir) where { extern castfn __cast (_: int):<> int dir }
end // end of [pavldiff_dir_get]

(* ****** ****** *)

fn{key:t0p;itm:vt0p}
  pavldiff_child_set
  {n,h:int} {chld:addr} {dir:int} {rt,rtp:addr}
  {slf:addr | slf <> rtp} {chld1:addr} (
  fpf: !pavldiff_v (key, itm, n, h, chld, dir, rt, rtp, slf)
         >> pavldiff_v (key, itm, n, h, chld1, dir, rt, rtp, slf)
  // end of [fpf]
| p: ptr slf, dir: int dir, pc1: ptr chld1
) :<> void =
  if dir = 0 then let
    prval B1L (pf_at, fpf1, pf2) = fpf
    val () = pavlnode_set_left<key,itm> (pf_at | p, pc1)
    prval () = fpf := B1L (pf_at, fpf1, pf2)
  in
    // nothing
  end else let
    prval B1R (pf_at, pf1, fpf2) = fpf
    val () = pavlnode_set_right<key,itm> (pf_at | p, pc1)
    prval () = fpf := B1R (pf_at, pf1, fpf2)
  in
    // nothing
  end // end of [if]
// end of [pavldiff_child_set]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
pavltree_split {h0:nat} {rt:addr} (
    pf: pavltree_v (key, itm, h0, null, rt)
  | p: &ptr rt >> ptr slf, k0: key, dir: &int 0 >> int dir, cmp: cmp key
  ) :<> #[dir:two;slf:addr] [h1:nat | h1 <= h0;chld:addr] (
    pavldiff_v (key, itm, h0, h1, chld, dir, rt, null, slf), pavltree_v (key, itm, h1, slf, chld)
  | ptr chld
  )
// end of [pavltree_split]

implement{key,itm} pavltree_split
  {h0} {rt} (pf | p, k0, dir, cmp) = let
  fun loop {h:nat | h <= h0}
    {chld:addr} {dir:two} {slf:addr} .<h>. (
    fpf: pavldiff_v (key, itm, h0, h, chld, dir, rt, null, slf)
  , pf: pavltree_v (key, itm, h, slf, chld)
  | p: &ptr slf >> ptr slf, pc: ptr chld, dir: &int dir >> int dir
  ) :<cloref> #[dir:two;slf:addr]
    [h1:nat | h1 <= h] [chld:addr] (
    pavldiff_v (key, itm, h0, h1, chld, dir, rt, null, slf)
  , pavltree_v (key, itm, h1, slf, chld)
  | ptr chld
  ) =
  if pc > null then let
    prval B (pf_at, pf_l, pf_r) = pf
    val sgn = compare_key_key (k0, pavlnode_get_key<key,itm> (pf_at | pc), cmp)
  in
    if sgn < 0 then let
      val p_tl = pavlnode_get_left<key,itm> (pf_at | pc) in
      p := pc;
      dir := 0(*left*);
      loop (B1L {key,itm} (pf_at, fpf, pf_r), pf_l | p, p_tl, dir)
    end else if sgn > 0 then let
      val p_tr = pavlnode_get_right<key,itm> (pf_at | pc) in
      p := pc;
      dir := 1(*right*);
      loop (B1R {key,itm} (pf_at, pf_l, fpf), pf_r | p, p_tr, dir)
    end else begin // sgn = 0
      (fpf, B (pf_at, pf_l, pf_r) | pc)
    end // end of [if]
  end else (fpf, pf | pc)
  // end of [if]
  val pc = p
in
  p := null;
  loop (E1 {key,itm} {h0} (), pf | p, pc, dir)
end // end of [pavltree_split]

(* ****** ****** *)

assume map_t0ype_viewt0ype_type (key:t0p, itm:vt0p) =
  [h:nat;slf:addr] (pavltree_v (key, itm, h, null, slf) | ptr slf)
// end of [map_vt]

(* ****** ****** *)

implement{} linmap_make_nil {key,itm} () = (E {key,itm} {null} () | null)

(* ****** ****** *)

implement{} linmap_is_nil {key,itm} (m) = m.1 = null
implement{} linmap_isnot_nil {key,itm} (m) = m.1 > null

(* ****** ****** *)

implement{key,itm}
linmap_size (m) = loop (m.0 | m.1) where {
  fun loop {h:nat} {pnt,slf:addr} .<h>. (
    pf: !pavltree_v (key, itm, h, pnt, slf)
  | p: ptr slf
  ) :<> size_t =
    if p > null then let
      prval B (pf_at, pfl, pfr) = pf
      val res = loop (pfl | pavlnode_get_left<key,itm> (pf_at | p))
                + size_of_int 1
                + loop (pfr | pavlnode_get_right<key,itm> (pf_at | p))
      // end of [val]
      prval () = pf := B (pf_at, pfl, pfr)
    in
      res
    end else size_of_int 0 // end of [if]
  // end of [loop]
} // end of [linmap_size]

(* ****** ****** *)

implement{key,itm}
linmap_height (m) = let val p = m.1 in
  if p > null then let
    prval B (pf_at, pfl, pfr) = m.0
    val h = pavlnode_get_height<key,itm> (pf_at | p)
    prval () = m.0 := B (pf_at, pfl, pfr)
  in
    h
  end else 0 // end of [if]
end // end of [linmap_height]

(* ****** ****** *)

implement{key,itm}
linmap_search (m, k0, cmp, res) = search (m.0 | m.1, res) where {
  fun search {h:nat} {pnt:addr} {slf:addr} .<h>. (
    pf: !pavltree_v (key, itm, h, pnt, slf)
  | p: ptr slf
  , res: &itm? >> opt (itm, tag)
  ) :<cloref> #[tag:bool] bool tag =
    if p > null then let
      prval B (pf_at, pfl, pfr) = pf
      val sgn = compare_key_key (k0, pavlnode_get_key<key,itm> (pf_at | p), cmp)
    in
      if sgn < 0 then let
        val tag = search (pfl | pavlnode_get_left<key,itm> (pf_at | p), res)
        prval () = pf := B (pf_at, pfl, pfr)
      in
        tag
      end else if sgn > 0 then let
        val tag = search (pfr | pavlnode_get_right<key,itm> (pf_at | p), res)
        prval () = pf := B (pf_at, pfl, pfr)
      in
        tag
      end else let
        val (pf_itm, fpf | p_itm) = pavlnode_takeout_val<key,itm> (pf_at | p)
        val () = res := !p_itm
        prval () = pf_at := fpf (pf_itm)
        prval () = opt_some {itm} (res)
        prval () = pf := B (pf_at, pfl, pfr)
      in
        true // item associated with the key [k0] is found
      end // end of [if]
    end else let
      prval () = opt_none {itm} (res) in false
    end // end of [if]
} // end of [linmap_search]

(* ****** ****** *)

local

fun{key:t0p;itm:vt0p} insert_rebalance
  {n0,h0:nat | h0 <= n0} {h1:nat | h0 <= h1; h1 <= h0+1}
  {chld0,chld1:addr} {dir:two} {rt:addr} {slf:addr} .<n0-h0>. (
  fpf: pavldiff_v (key, itm, n0, h0, chld0, dir, rt, null, slf)
, pf0: pavltree_v (key, itm, h1, slf, chld1)
| h0: int h0, pc0: ptr chld0, dir: int dir, pt: ptr rt, p: ptr slf
, pc1: ptr chld1
) :<> [slf:addr] (
  pavltree_v_inc (key, itm, n0, null, slf)
| ptr slf
) =
  if p > null then let
    val h1 = pavltree_height_get (pf0 | pc1)
  in
    if h0 = h1 then begin
      pavldiff_child_set<key,itm> (fpf | p, dir, pc1);
      (pavldiff_pavltree_join {key,itm} (fpf, pf0) | pt)
    end else begin // [h1 = h0+1]
      if dir = 0 then let
        prval B1L (pf_at, fpf1, pf2) = fpf
        val pp = pavlnode_get_parent<key,itm> (pf_at | p)
        val h0p = pavlnode_get_height<key,itm> (pf_at | p)
        val dirp = pavldiff_dir_get (fpf1 | pp, p)
        val () = pavlnode_set_left<key,itm> (pf_at | p, pc1)
        val h0r = pavltree_height_get<key,itm> (pf2 | pavlnode_get_right<key,itm> (pf_at | p))
      in
        if h1 = h0r + 2 then let
          val (pf0_new | p_new) = pavltree_rrotate<key,itm> (pf_at, pf0, pf2 | p)
        in
          insert_rebalance<key,itm> (fpf1, pf0_new | h0p, p, dirp, pt, pp, p_new)
        end else let
          val () = pavlnode_set_height<key,itm> (pf_at | p, max (h1, h0r)+1)
          prval pf0_new = B {key,itm} (pf_at, pf0, pf2)
        in
          insert_rebalance<key,itm> (fpf1, pf0_new | h0p, p, dirp, pt, pp, p)
        end // end of [if]
      end else let
        prval B1R (pf_at, pf1, fpf2) = fpf
        val pp = pavlnode_get_parent<key,itm> (pf_at | p)
        val h0p = pavlnode_get_height<key,itm> (pf_at | p)
        val dirp = pavldiff_dir_get (fpf2 | pp, p)
        val () = pavlnode_set_right<key,itm> (pf_at | p, pc1)
        val h0l = pavltree_height_get<key,itm> (pf1 | pavlnode_get_left<key,itm> (pf_at | p))
      in
        if h1 = h0l + 2 then let
          val (pf0_new | p_new) = pavltree_lrotate<key,itm> (pf_at, pf1, pf0 | p)
        in
          insert_rebalance<key,itm> (fpf2, pf0_new | h0p, p, dirp, pt, pp, p_new)
        end else begin
          pavlnode_set_height<key,itm> (pf_at | p, max (h0l, h1)+1);
          insert_rebalance<key,itm> (fpf2, B {key,itm} (pf_at, pf1, pf0) | h0p, p, dirp, pt, pp, p)
        end // end of [if]
      end // end of [if]
    end // end of [if]
  end else let
    prval E1 () = fpf in (pf0 | pc1)
  end // end of [if]
// end of [insert_rebalance]

in // in of [local]

implement{key,itm}
linmap_insert {l_at} (pf_at | m, p_at, cmp) = let
  prval () = pavlnode_ptr_is_gtz (pf_at)
  var pt = m.1
  var p = pt
  val k0 = pavlnode_get_key<key,itm> (pf_at | p_at)
  var dir = 0
  val (fpf, pf0 | pc0) = pavltree_split (m.0 | p, k0, dir, cmp)
in
  if pc0 > null then let // key already exists
    // swap the two nodes
    fn{key:t0p;itm:vt0p}
      pavldiff_child_set_opt
      {n,h:int} {chld:addr} {dir:int} {rt:addr}
      {slf:addr} {chld1:addr} (
      fpf: !pavldiff_v (key, itm, n, h, chld, dir, rt, null, slf)
            >> pavldiff_v (key, itm, n, h, chld1, dir, rt1, null, slf)
      // end of [fpf]
    | pt: &ptr rt >> ptr rt1, p: ptr slf, dir: int dir, pc0: ptr chld, pc1: ptr chld1
    ) :<> #[rt1:addr] void =
      if p = null then let
        prval E1 () = fpf
        prval () = fpf := E1 {key,itm} {n} {chld1} {dir} {slf} ()
      in
        pt := pc1
      end else pavldiff_child_set (fpf | p, dir, pc1)
    // end of [pavldiff_child_set_opt]
    fn pavldiff_pavltree_swap
      {n,h:nat | h <= n} {chld1,chld2:agz} {dir:two} {rt:addr;slf:addr} (
        fpf: !pavldiff_v (key, itm, n, h, chld1, dir, rt, null, slf)
              >> pavldiff_v (key, itm, n, h, chld2, dir, rt1, null, slf)
      , pf0: !pavltree_v (key, itm, h, slf, chld1)
              >> pavltree_v (key, itm, h, slf, chld2)
      , pf_at: pavlnode0_v (key, itm, chld2)
      | pt: &ptr rt >> ptr rt1
      , p0: ptr chld1
      , dir: int dir
      , p_at: &ptr chld2 >> ptr chld1
      ) :<> #[rt1:addr] (
        pavlnode0_v (key, itm, chld1)
      | void
      ) = let
      prval B (pf0_at, pf0_tl, pf0_tr) = pf0
      val p_tl = pavlnode_get_left (pf0_at | p0)
      and p_tr = pavlnode_get_right (pf0_at | p0)
      and pp = pavlnode_get_parent (pf0_at | p0)
      val () = pavltree_parent_set (pf0_tl | p_tl, p_at)
      val () = pavltree_parent_set (pf0_tr | p_tr, p_at)
      val () = pavlnode_set_height (pf_at | p_at, pavlnode_get_height (pf0_at | p0))
      val () = pavlnode_set_left (pf_at | p_at, p_tl)
      val () = pavlnode_set_right (pf_at | p_at, p_tr)
      val () = pavlnode_set_parent (pf_at | p_at, pp)
      val () = pavldiff_child_set_opt (fpf | pt, pp, dir, p0, p_at)
      prval () = pf0 := B {key,itm} (pf_at, pf0_tl, pf0_tr)
    in
      p_at := p0;
      (pf0_at | ())
    end // end of [pavldiff_pavltree_swap]
    val (pf0_at | ()) = pavldiff_pavltree_swap (fpf, pf0, pf_at | pt, pc0, dir, p_at)
    prval pf = pavldiff_pavltree_join {key,itm} (fpf, pf0)
    prval () = pf_at := Some_v (pf0_at)
    prval () = m.0 := pf
    val () = m.1 := pt
  in
    true // swapped the two elements
  end else let
    prval E () = pf0
    val () = pavlnode_set_height<key,itm> (pf_at | p_at, 1)
    val () = pavlnode_set_parent<key,itm> (pf_at | p_at, p)
    val () = pavlnode_set_left<key,itm> (pf_at | p_at, null)
    val () = pavlnode_set_right<key,itm> (pf_at | p_at, null)
    prval pf0 = B {key,itm} (pf_at, E (), E ())
    prval () = pf_at := None_v ()
    val (pf | p_new) = insert_rebalance<key,itm> (fpf, pf0 | 0, pc0, dir, pt, p, p_at)
    prval () = m.0 := pf
  in
    m.1 := p_new; false // insertion is performed
  end // end of [if]
end // end of [linmap_insert]

end // end of [local]

(* ****** ****** *)

local

fun{key:t0p;itm:vt0p} remove_rebalance
  {n0,h0:nat | h0 <= n0}
  {h1:nat | h1 <= h0; h0 <= h1+1}
  {chld0,chld1:addr} {dir:two} {rt:addr}
  {slf:addr} .<n0-h0>. (
    fpf: pavldiff_v (key, itm, n0, h0, chld0, dir, rt, null, slf)
  , pf0: pavltree_v (key, itm, h1, slf, chld1)
  | h0: int h0, pc0: ptr chld0, dir: int dir, pt: ptr rt, p: ptr slf
  , pc1: ptr chld1
  ) :<> [slf:addr] (
    pavltree_v_dec (key, itm, n0, null, slf)
  | ptr slf
  ) =
  if p > null then let
    val h1 = pavltree_height_get (pf0 | pc1)
  in
    if h0 = h1 then begin
      pavldiff_child_set<key,itm> (fpf | p, dir, pc1);
      (pavldiff_pavltree_join {key,itm} (fpf, pf0) | pt)
    end else begin // h0 = h1 + 1
      if dir = 0 then let
        prval B1L (pf_at, fpf1, pf2) = fpf
        val pp = pavlnode_get_parent (pf_at | p)
        val h0p = pavlnode_get_height (pf_at | p)
        val dirp = pavldiff_dir_get (fpf1 | pp, p)
        val () = pavlnode_set_left (pf_at | p, pc1)
        val h0r = pavltree_height_get (pf2 | pavlnode_get_right (pf_at | p))
      in
        if h0r = h1 + 2 then let
          val (pf0_new | p_new) =
            pavltree_lrotate<key,itm> (pf_at, pf0, pf2 | p)
          // end of [val]
        in
          remove_rebalance<key,itm> (fpf1, pf0_new | h0p, p, dirp, pt, pp, p_new)
        end else begin
          pavlnode_set_height<key,itm> (pf_at | p, max (h1, h0r)+1);
          remove_rebalance<key,itm> (fpf1, B {key,itm} (pf_at, pf0, pf2) | h0p, p, dirp, pt, pp, p)
        end // end of [if]
      end else let
        prval B1R (pf_at, pf1, fpf2) = fpf
        val pp = pavlnode_get_parent (pf_at | p)
        val h0p = pavlnode_get_height (pf_at | p)
        val dirp = pavldiff_dir_get (fpf2 | pp, p)
        val () = pavlnode_set_right (pf_at | p, pc1)
        val h0l = pavltree_height_get (pf1 | pavlnode_get_left (pf_at | p))
      in
        if h0l = h1 + 2 then let
          val (pf0_new | p_new) =
            pavltree_rrotate<key,itm> (pf_at, pf1, pf0 | p)
          // end of [val]
        in
          remove_rebalance<key,itm> (fpf2, pf0_new | h0p, p, dirp, pt, pp, p_new)
        end else begin
          pavlnode_set_height<key,itm> (pf_at | p, max (h0l, h1) + 1);
          remove_rebalance<key,itm> (fpf2, B {key,itm} (pf_at, pf1, pf0) | h0p, p, dirp, pt, pp, p)
        end // end of [if]
      end // end of [if]
    end // end of [if]
  end else let
    prval E1 () = fpf in (pf0 | pc1)
  end // end of [if]
// end of [remove_rebalance]

fn{key:t0p;itm:vt0p}
  pavltree_pavltree_join
  {hl,hr:nat | hl <= hr+1; hr <= hl+1}
  {lft,rgh,pnt1,pnt2:addr} (
  pf_tl: pavltree_v (key, itm, hl, pnt1, lft)
, pf_tr: pavltree_v (key, itm, hr, pnt2, rgh)
| pl: ptr lft, pr: ptr rgh
) :<> [pnt,slf:addr] (
  pavltree_v_inc (key, itm, max(hl,hr), pnt, slf)
| ptr slf
) = let
  viewdef pavlnode_v (key:t@ype, itm:viewt@ype, lft: addr, slf:addr) =
    [h:nat] [rgh,pnt:addr] pavlnode_v (key, itm, h, lft, rgh, pnt, slf)
  // end of [pavlnode_v]
  fun loop
    {h0:nat | h0 <= hl}
    {chld:addr | chld > null}
    {rt:addr} {slf:addr} .<h0>. (
    fpf: pavldiff_v (key, itm, hl, h0, chld, 1(*right*), rt, null, slf)
  , pf0: pavltree_v (key, itm, h0, slf, chld) // view for the missing avltree
  | pc: ptr (chld), pt: ptr rt, p: ptr slf
  ) :<> [slf:agz] [lft:addr]  (
    pavlnode_v (key, itm, lft, slf), pavltree_v_dec (key, itm, hl, slf, lft) | ptr slf
  ) = let
    prval B (pf0_at, pf0_l, pf0_r) = pf0
    val pc_r = pavlnode_get_right<key,itm> (pf0_at | pc)
  in
    if pc_r > null then let
      prval fpf = B1R {key,itm} (pf0_at, pf0_l, fpf)
    in
      loop (fpf, pf0_r | pc_r, pt, pc)
    end else let
      prval E () = pf0_r
      val pc_l = pavlnode_get_left<key,itm> (pf0_at | pc)
      val () = pavltree_parent_set<key,itm> (pf0_l | pc_l, p)
      val (pf | pt) = remove_rebalance<key,itm>
        (fpf, pf0_l | pavlnode_get_height (pf0_at | pc), pc, 1(*right*), pt, p, pc_l)
    in
      pavlnode_set_left<key,itm> (pf0_at | pc, pt);
      pavltree_parent_set<key,itm> (pf | pt, pc);
      (pf0_at, pf | pc)
    end // end of [if]
  end // end of [loop]
in
  if pl > null then let
    prval fpf = E1 ()
    val () = pavltree_parent_set (pf_tl | pl, null)
    val (pf_at, pf_tl | p_at) = loop (fpf, pf_tl | pl, pl, null)
    val () = pavlnode_set_right (pf_at | p_at, pr)
    val () = pavltree_parent_set<key,itm> (pf_tr | pr, p_at)
    val pl = pavlnode_get_left (pf_at | p_at)
    val hl = pavltree_height_get<key,itm> (pf_tl | pl)
    val hr = pavltree_height_get<key,itm> (pf_tr | pr)
  in
    if hl+2 = hr then begin
      pavltree_lrotate<key,itm> (pf_at, pf_tl, pf_tr | p_at)
    end else begin
      pavlnode_set_height<key,itm> (pf_at | p_at, max(hl,hr)+1);
      (B (pf_at, pf_tl, pf_tr) | p_at)
    end // end of [if]
  end else let
    prval E () = pf_tl in (pf_tr | pr)
  end // end of [if]
end // end of [pavltree_pavltree_join]

in // in of [local]

implement{key,itm}
linmap_takeout (m, k0, cmp) = let
  val pt = m.1
  var p = pt
  var dir = 0
  val [h1:int,chld:addr] (fpf, pf0 | pc0) =
    pavltree_split (m.0 | p, k0, dir, cmp)
  // end of [val]
  viewdef V = pavlnode0_v (key, itm, chld)
  prval () = ptr_is_gtez (pc0)
in
  if pc0 > null then let
    prval B (pf0_at, pf0_tl, pf0_tr) = pf0
    val (pf0 | pc0_new) = pavltree_pavltree_join<key,itm> (
      pf0_tl, pf0_tr
    | pavlnode_get_left<key,itm> (pf0_at | pc0)
    , pavlnode_get_right<key,itm> (pf0_at | pc0)
    ) // end of [val]
    val () = pavltree_parent_set (pf0 | pc0_new, p)
    val (pf_new | pt_new) =
      remove_rebalance<key,itm> (fpf, pf0 | pavlnode_get_height (pf0_at | pc0), pc0, dir, pt, p, pc0_new)
    // end of [val]
  in
    // removed
    m.0 := pf_new;
    m.1 := pt_new;
    (Some_v {V} (pf0_at) | pc0)
  end else let
    prval pf = pavldiff_pavltree_join {key,itm} (fpf, pf0)
  in
    // not removed
    m.0 := pf;
    (None_v {V} () | null)
  end // end of [if]
end // end of [linmap_takeout]

end // end of [local]

(* ****** ****** *)

implement{key,itm}
linmap_remove (m, k0, cmp) = let
  val (pf | p) = linmap_takeout<key,itm> (m, k0, cmp)
in
  if p > null then let
    prval Some_v (pf_nod) = pf
  in
    pavlnode_free<key,itm> (pf_nod | p); true
  end else let
    prval None_v () = pf in false
  end // end of [if]
end // end of [linmap_remove]

(* ****** ****** *)
//
// AS: declarations for supporting iterative traversal
//
dataview pavlenum_v
  (key:t0p, itm:vt0p, int, int, addr, addr) =
  | {n,h:nat | h <= n} {chld:agz} {dir:two} {rt,slf:addr}
    pavlenum_v_some (key, itm, n, h, rt, chld) of (
      pavldiff_v (key, itm, n, h, chld, dir, rt, null, slf)
    , pavltree_v (key, itm, h, slf, chld)
    ) // end of [pavlenum_v_some]
  | {n:nat} {rt:addr} pavlenum_v_none (key, itm, n, n, rt, null) of (
      pavltree_v (key, itm, n, null, rt)
    ) // end of [pavlenum_v_none]
// end of [pavlenum_v]

prfn pavlenum_v_free
  {key:t0p;itm:vt0p}
  {h,h1:int} {slf,chld:addr} (
  pf: pavlenum_v (key, itm, h, h1, slf, chld)
) :<> pavltree_v (key, itm, h, null, slf) =
  sif chld > null then let
    prval pavlenum_v_some (fpf, pf0) = pf in
    pavldiff_pavltree_join {key,itm} (fpf, pf0)
  end else let
    prval pavlenum_v_none pf0 = pf in
    pf0
  end // end of [sif]
// end of [pavlenum_v_free]

local
//
// AS-2012-02:
// returns the node with the minimum value in the given (sub)tree
//
fun{
key:t0p;itm:vt0p
} min_value1
  {n,h:nat} {chld:agz} {rt:addr} .<h>. (
    pf: pavlenum_v (key, itm, n, h, rt, chld)
  | p: ptr chld
  ) :<> [h1:nat | h1 <= h] [chld1:agz] (
    pavlenum_v (key, itm, n, h1, rt, chld1)
  | ptr chld1
  ) = let
  prval pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) = pf
  val p_tl = pavlnode_get_left<key,itm> (pf_at | p)
in
  if p_tl > null then begin
    min_value1 (pavlenum_v_some (B1L (pf_at, fpf, pf_tr), pf_tl) | p_tl)
  end else begin
    (pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) | p)
  end // end of [if]
end // end of [min_value1]

fn{
key:t0p;itm:vt0p
} start_inord
  {h:nat} {chld:addr} (
  pf: pavltree_v (key, itm, h, null, chld)
| p: ptr chld
) :<> [h1:int] [chld1:addr] (
  pavlenum_v (key, itm, h, h1, chld, chld1)
| ptr chld1
) =
  if p > null then let
    prval fpf = E1 ()
    prval pf1 = pavlenum_v_some {key,itm} {h,h} {chld} {0} (fpf, pf)
  in
    min_value1<key,itm> (pf1 | p)
  end else begin
    (pavlenum_v_none (pf) | null)
  end // end of [if]
// end of [start_inord]

//
// AS: steps to the successor
//
fn{key:t0p;itm:vt0p}
  step_inord {n,h:int} {chld:agz;slf:addr} (
    pf: pavlenum_v (key, itm, n, h, slf, chld)
  | p: ptr chld
  ) :<> [h1:nat] [chld1:addr] (
    pavlenum_v (key, itm, n, h1, slf, chld1)
  | ptr chld1
  ) = let
  fun loop
    {n,h:nat | h <= n} {chld:agz;rt:addr} .<n-h>. (
      pf: pavlenum_v (key, itm, n, h, rt, chld)
    | p: ptr chld
    ) :<> [h1:nat | h <= h1; h1 <= n] [chld1:addr] (
      pavlenum_v (key, itm, n, h1, rt, chld1)
    | ptr chld1
    ) = let
    prval pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) = pf
    val pp = pavlnode_get_parent<key,itm> (pf_at | p)
    prval pf0 = B (pf_at, pf_tl, pf_tr)
    val dir = pavldiff_dir_get (fpf | pp, p)
  in
    if pp > null then begin
      if dir = 0(*left*) then let
        prval B1L (pf_at, fpf1, pf1) = fpf
      in
        (pavlenum_v_some {key,itm} (fpf1, B {key,itm} (pf_at, pf0, pf1)) | pp)
      end else let // dir = 1
        prval B1R (pf_at, pf1, fpf1) = fpf
        prval fpf0 = pavlenum_v_some {key,itm} (fpf1, B {key,itm} (pf_at, pf1, pf0))
      in
        loop (fpf0 | pp)
      end // end of [if]
    end else let
      prval fpf0 = pavldiff_pavltree_join {key,itm} (fpf, pf0)
    in
      (pavlenum_v_none fpf0 | null)
    end // end of [if]
  end // end of [loop]
  prval pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) = pf
  val p_tr = pavlnode_get_right<key,itm> (pf_at | p)
in
  if p_tr > null then let
    prval pf = pavlenum_v_some (B1R (pf_at, pf_tl, fpf), pf_tr) in
    min_value1<key,itm> (pf | p_tr)
  end else let
    prval pf = pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) in
    loop (pf | p)
  end // end of [if]
end // end of [step_inord]

fn{
key:t0p;itm:vt0p
} foreach_looping1
  {h:nat} {slf:addr} (
  pf1: !pavltree_v (key, itm, h, null, slf)
| p: ptr slf
, f: (key, &itm) -<fun> void
) : void = let
  val (pf | p1) = start_inord (pf1 | p)
  fun loop {n,h:int} {chld,rt:addr} (
      pfe: pavlenum_v (key, itm, n, h, rt, chld)
    | pe: ptr chld
    ) :<cloref1> (
      pavltree_v (key, itm, n, null, rt) | void
    ) =
    if pe > null then let
      prval pavlenum_v_some (fpf, B (pf_nod, pf_tl, pf_tr)) = pfe
      val k = pavlnode_get_key<key,itm> (pf_nod | pe)
      val (pf_at, fpf_at | p_at) = pavlnode_takeout_val<key,itm> (pf_nod | pe)
      val () = f (k, !p_at)
      prval () = pf_nod := fpf_at {itm} (pf_at)
      prval pfe = pavlenum_v_some (fpf, B (pf_nod, pf_tl, pf_tr))
      val (pfe | pe) = step_inord<key,itm> (pfe | pe)
    in
      loop (pfe | pe)
    end else begin
      (pavlenum_v_free {key,itm} (pfe) | ())
    end // end of [if]
  val (pf | ()) = loop (pf | p1)
  prval () = pf1 := pf
in
  // nothing
end // end of [foreach_looping1]

in // of [local]

implement{key,itm}
linmap_foreach_fun_iter (m, f) = (
  // AS: for not having to prove termination
  $effmask_all (foreach_looping1<key,itm> (m.0 | m.1, f))
) // end of [linmap_foreach_fun_iter]

end // end of [local]

local
//
// AS-2012-02:
// returns the node with the maximum value in the given (sub)tree
//
fun{key:t0p;itm:vt0p} max_value1
  {n,h:nat} {chld:agz} {rt:addr} .<h>. (
    pf: pavlenum_v (key, itm, n, h, rt, chld)
  | p: ptr chld
  ) :<> [h1:nat | h1 <= h] [chld1:agz] (
    pavlenum_v (key, itm, n, h1, rt, chld1)
  | ptr chld1
  ) = let
  prval pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) = pf
  val p_tr = pavlnode_get_right<key,itm> (pf_at | p)
in
  if p_tr > null then begin
    max_value1 (pavlenum_v_some (B1R (pf_at, pf_tl, fpf), pf_tr) | p_tr)
  end else begin
    (pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) | p)
  end // end of [if]
end // end of [max_value1]

fn{
key:t0p;itm:vt0p
} start_preord
  {h:nat} {chld:addr} (
  pf: pavltree_v (key, itm, h, null, chld)
| p: ptr chld
) :<> [h1:int] [chld1:addr] (
  pavlenum_v (key, itm, h, h1, chld, chld1)
| ptr chld1
) =
  if p > null then let
    prval fpf = E1 ()
    prval pf1 = pavlenum_v_some {key,itm} {h,h} {chld} {0} (fpf, pf)
  in
    max_value1<key,itm> (pf1 | p)
  end else begin
    (pavlenum_v_none (pf) | null)
  end // end of [if]
// end of [start_preord]

//
// AS: steps to the predecessor
fn{
key:t0p;itm:vt0p
} step_preord
  {n,h:int} {chld:agz;slf:addr} (
    pf: pavlenum_v (key, itm, n, h, slf, chld)
  | p: ptr chld
  ) :<> [h1:nat] [chld1:addr] (
    pavlenum_v (key, itm, n, h1, slf, chld1)
  | ptr chld1
  ) = let
  fun loop
    {n,h:nat | h <= n} {chld:agz;rt:addr} .<n-h>. (
      pf: pavlenum_v (key, itm, n, h, rt, chld)
    | p: ptr chld
    ) :<> [h1:nat | h <= h1; h1 <= n] [chld1:addr] (
      pavlenum_v (key, itm, n, h1, rt, chld1)
    | ptr chld1
    ) = let
    prval pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) = pf
    val pp = pavlnode_get_parent<key,itm> (pf_at | p)
    prval pf0 = B (pf_at, pf_tl, pf_tr)
    val dir = pavldiff_dir_get (fpf | pp, p)
  in
    if pp > null then begin
      if dir = 0(*left*) then let
        prval B1L (pf_at, fpf1, pf1) = fpf
        prval fpf0 = pavlenum_v_some {key,itm} (fpf1, B {key,itm} (pf_at, pf0, pf1))
      in
        loop (fpf0 | pp)
      end else let // dir = 1
        prval B1R (pf_at, pf1, fpf1) = fpf
        prval fpf0 = pavlenum_v_some {key,itm} (fpf1, B {key,itm} (pf_at, pf1, pf0))
      in
        (fpf0 | pp)
      end // end of [if]
    end else let
      prval fpf0 = pavldiff_pavltree_join {key,itm} (fpf, pf0)
    in
      (pavlenum_v_none fpf0 | null)
    end // end of [if]
  end // end of [loop]
  prval pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) = pf
  val p_tl = pavlnode_get_left<key,itm> (pf_at | p)
in
  if p_tl > null then let
    prval pf = pavlenum_v_some (B1L (pf_at, fpf, pf_tr), pf_tl) in
    max_value1<key,itm> (pf | p_tl)
  end else let
    prval pf = pavlenum_v_some (fpf, B (pf_at, pf_tl, pf_tr)) in
    loop (pf | p)
  end // end of [if]
end // end of [step_preord]

fn{
key:t0p;itm:vt0p
} rforeach_looping1
  {h:nat} {slf:addr} (
  pf1: !pavltree_v (key, itm, h, null, slf)
| p: ptr slf
, f: (key, &itm) -<fun> void
) : void = let
  val (pf | p1) = start_preord (pf1 | p)
  fun loop {n,h:int} {chld,rt:addr} (
      pfe: pavlenum_v (key, itm, n, h, rt, chld)
    | pe: ptr chld
    ) :<cloref1> (
      pavltree_v (key, itm, n, null, rt)
    | void
    ) =
    if pe > null then let
      prval pavlenum_v_some (fpf, B (pf_nod, pf_tl, pf_tr)) = pfe
      val k = pavlnode_get_key<key,itm> (pf_nod | pe)
      val (pf_at, fpf_at | p_at) = pavlnode_takeout_val<key,itm> (pf_nod | pe)
      val () = f (k, !p_at)
      prval () = pf_nod := fpf_at {itm} (pf_at)
      prval pfe = pavlenum_v_some (fpf, B (pf_nod, pf_tl, pf_tr))
      val (pfe | pe) = step_preord<key,itm> (pfe | pe)
    in
      loop (pfe | pe)
    end else begin
      (pavlenum_v_free {key,itm} (pfe) | ())
    end // end of [if]
  val (pf | ()) = loop (pf | p1)
  prval () = pf1 := pf
in
  // nothing
end // end of [rforeach_looping1]

in // in of [local]

implement{key,itm}
linmap_rforeach_fun_iter (m, f) = (
  // AS: for not having to prove termination
  $effmask_all (rforeach_looping1<key,itm> (m.0 | m.1, f))
) // end of [linmap_rforeach]

end // end of [local]

(* ****** ****** *)

implement{key,itm}
linmap_foreach_funenv {v} {vt}
  (pf | m, f, env) =
  foreach (pf, m.0 | m.1, env) where {
//
fun foreach
  {h:nat} {pnt,slf:addr} .<h>. (
  pfv: !v
, pf1: !pavltree_v (key, itm, h, pnt, slf)
| p: ptr slf, env: !vt
) :<cloref> void =
  if p > null then let
    prval B (pf_nod, pf_tl, pf_tr) = pf1
    val k = pavlnode_get_key<key,itm> (pf_nod | p)
    and p_tl = pavlnode_get_left<key,itm> (pf_nod | p)
    and p_tr = pavlnode_get_right<key,itm> (pf_nod | p)
    val () = foreach (pfv, pf_tl | p_tl, env)
    val (pf_at, fpf | p_at) = pavlnode_takeout_val<key,itm> (pf_nod | p)
    val () = f (pfv | k, !p_at, env)
    prval () = pf_nod := fpf {itm} (pf_at)
    val () = foreach (pfv, pf_tr | p_tr, env)
    prval () = pf1 := B (pf_nod, pf_tl, pf_tr)
  in
    // nothing
  end else let
    prval E () = pf1; prval () = pf1 := E () in
    // nothing
  end // end of [if]
// end of [foreach]
} // end of [linmap_foreach_funenv]

implement{key,itm}
linmap_foreach_fun
  (m, f) = let
//
  val f = coerce (f) where {
    extern castfn coerce
      (f: (key, &itm) -<fun> void):<> (!unit_v | key, &itm, !ptr) -<fun> void
  } // end of [val]
//
  prval pfu = unit_v ()
  val () = linmap_foreach_funenv<key,itm> {unit_v} {ptr} (pfu | m, f, null)
  prval unit_v () = pfu
//
in
  // nothing
end // end of [linmap_foreach_fun]

(* ****** ****** *)

implement{key,itm}
linmap_foreach_vclo {v}
  (pf | m, f) =
  foreach (pf, m.0 | m.1, f) where {
//
fun foreach
  {h:nat} {pnt,slf:addr} .<h>. (
  pfv: !v
, pf1: !pavltree_v (key, itm, h, pnt, slf)
| p: ptr slf
, f: &(!v | key, &itm) -<clo> void
) :<> void =
  if p > null then let
    prval B (pf_nod, pf_tl, pf_tr) = pf1
    val k = pavlnode_get_key<key,itm> (pf_nod | p)
    and p_tl = pavlnode_get_left<key,itm> (pf_nod | p)
    and p_tr = pavlnode_get_right<key,itm> (pf_nod | p)
    val () = foreach (pfv, pf_tl | p_tl, f)
    val (pf_at, fpf | p_at) = pavlnode_takeout_val<key,itm> (pf_nod | p)
    val () = f (pfv | k, !p_at)
    prval () = pf_nod := fpf {itm} (pf_at)
    val () = foreach (pfv, pf_tr | p_tr, f)
    prval () = pf1 := B (pf_nod, pf_tl, pf_tr)
  in
    // nothing
  end else let
    prval E () = pf1; prval () = pf1 := E ()
  in
    // nothing
  end // end of [if]
// end of [foreach]
} // end of [linmap_foreach_vclo]

(* ****** ****** *)

implement{key,itm}
linmap_rforeach_funenv {v} {vt}
  (pf | m, f, env) =
  rforeach (pf, m.0 | m.1, env) where {
//
fun rforeach
  {h:nat} {pnt,slf:addr} .<h>. (
  pfv: !v
, pf1: !pavltree_v (key, itm, h, pnt, slf)
| p: ptr slf, env: !vt
) :<cloref> void =
  if p > null then let
    prval B (pf_nod, pf_tl, pf_tr) = pf1
    val k = pavlnode_get_key<key,itm> (pf_nod | p)
    and p_tl = pavlnode_get_left<key,itm> (pf_nod | p)
    and p_tr = pavlnode_get_right<key,itm> (pf_nod | p)
    val () = rforeach (pfv, pf_tr | p_tr, env)
    val (pf_at, fpf | p_at) = pavlnode_takeout_val<key,itm> (pf_nod | p)
    val () = f (pfv | k, !p_at, env)
    prval () = pf_nod := fpf {itm} (pf_at)
    val () = rforeach (pfv, pf_tl | p_tl, env)
    prval () = pf1 := B (pf_nod, pf_tl, pf_tr)
  in
    // nothing
  end else let
    prval E () = pf1; prval () = pf1 := E () in
    // nothing
  end // end of [if]
// end of [foreach]
} // end of [linmap_rforeach_funenv]

(* ****** ****** *)

implement{key,itm}
linmap_clear_funenv
  {v} {vt} (
  pfv | m, f, env
) = let
  typedef FT1 = (!v | key, &itm >> itm?, !vt) -<fun> void
  typedef FT2 = (!v | key, &itm >> itm , !vt) -<fun> void
  val () = let
    extern castfn __cast (f: FT1):<> FT2
  in
    linmap_foreach_funenv (pfv | m, __cast(f), env)
  end // end of [val]
  prval () = __assert (m) where {
    extern praxi __assert (m: !map (key, itm) >> map (key, itm?)): void
  } // end of [val]
in
  // nothing
end // end of [linmap_clear_funenv]

(* ****** ****** *)

implement{key,itm}
linmap_free (m) = let
// freeing is done in the inord fashion
fun _free
  {h:nat} {pnt,slf:addr} .<h>. (
  pf1: pavltree_v (key, itm, h, pnt, slf) | p: ptr slf
) :<cloref> void =
  if p > null then let
    prval B (pf_nod, pf_tl, pf_tr) = pf1
    val p_tl = pavlnode_get_left<key,itm> (pf_nod | p)
    and p_tr = pavlnode_get_right<key,itm> (pf_nod | p)
    val () = pavlnode_free<key,itm> (pf_nod | p)
    val () = _free (pf_tl | p_tl)
    and () = _free (pf_tr | p_tr)
  in
    // nothing
  end else let
    prval E () = pf1
  in
    // nothing
  end // end of [if]
// end of [_free]
in
  _free (m.0 | m.1)
end // end of [linmap_free]

(* ****** ****** *)

implement{key,itm}
linmap_free_vt (m) =
  if m.1 > null then let
    prval () = opt_some {map (key, itm)} (m)
  in
    true
  end else let // m.1 = null
    prval E () = m.0
    prval () = opt_none {map (key, itm)} (m)
  in
    false
  end // end of [if]
// end of [linmap_free_vt]

(* ****** ****** *)

(* end of [linmap_pavltree.dats] *)
