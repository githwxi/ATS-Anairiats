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
** A map implementation based on AVL trees
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by
**   Artyom Shalkhakov (artyom DOT shalkhakov AT gmail DOT com)
** Time: January, 2012 // based on a version done by HX in May, 2010
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

staload "libats/ngc/SATS/linmap_avltree.sats"

(* ****** ****** *)
//
// a specialized version can be implemented on the spot
//
implement{key}
compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)
//
// HX-2010-03-24: this seems to work best!
//
#define HTDF 1 // max height difference
#define HTDF1 %(HTDF+1)
#define HTDF_1 %(HTDF-1)

(* ****** ****** *)

dataview
avltree_v (
  key:t@ype
, itm:viewt@ype+
, int(*height*)
, addr(*self*)
) =
  | {ll,lr:addr}
    {hl,hr:nat | hl <= hr+HTDF; hr <= hl+HTDF}
    {h:int | h == 1+max(hl,hr)}
    {slf:agz}
    B (key, itm, h, slf) of (
        avlnode_v (key, itm, h, ll, lr, slf)
      , avltree_v (key, itm, hl, ll)
      , avltree_v (key, itm, hr, lr)
      ) // end of [B]
  | E (key, itm, 0, null)
// end of [dataview avltree_v]

viewdef
avltree_v_inc (key:t@ype, itm:viewt@ype, h:int, l:addr) =
  [h1:nat | h <= h1; h1 <= h+1] avltree_v (key, itm, h1, l)
// end of [avltree_v_inc]

viewdef
avltree_v_dec (key:t@ype, itm:viewt@ype, h:int, l:addr) =
  [h1:nat | h1 <= h; h <= h1+1] avltree_v (key, itm, h1, l)
// end of [avltree_v_dec]

(* ****** ****** *)

assume
map_t0ype_viewt0ype_type (
  key:t@ype, itm:viewt@ype
) = [l:addr] [h:nat] (avltree_v (key, itm, h, l) | ptr l)
// end of [map_t0ype_viewt0ype_type]

(* ****** ****** *)

implement{} linmap_make_nil () = (E () | null)

(* ****** ****** *)

implement{} linmap_is_nil (t) = t.1 = null
implement{} linmap_isnot_nil (t) = t.1 > null

(* ****** ****** *)

implement{key,itm}
linmap_size (t) =
  size (t.0 | t.1) where {
  fun size {h:nat} {l:addr} .<h>. (
    pf: !avltree_v (key, itm, h, l)
  | p: ptr l
  ) :<> size_t =
    if p > null then let
      prval B (pf_at, pf_l, pf_r) = pf
      val res =
        size (pf_l | avlnode_get_left<key,itm> (pf_at | p))
        + 1
        + size (pf_r | avlnode_get_right<key,itm> (pf_at | p))
      // end of [val]
      prval () = pf := B (pf_at, pf_l, pf_r)
    in
      res
    end else size_of_int 0 // end of [if]
  // end of [size]
} // end of [where]

(* ****** ****** *)

fn{key:t0p;itm:vt0p}
avltree_height {h:nat} {l:addr} (
  pf: !avltree_v (key, itm, h, l) | p: ptr l
) :<> int h =
  if p > null then let
    prval B (pf_at, pf_l, pf_r) = pf
    val h = avlnode_get_height<key,itm> (pf_at | p)
    prval () = pf := B (pf_at, pf_l, pf_r)
  in
    h
  end else let
    prval E () = pf; prval () = pf := E {key,itm} ()
  in
    0
  end // end of [if]
// end of [avltree_height]

implement{key,itm} linmap_height (t) = avltree_height (t.0 | t.1)

(* ****** ****** *)

implement{key,itm}
linmap_search
  (t, k0, cmp, res) = search (t.0 | t.1, res) where {
  fun search {h:nat} {slf:addr} .<h>. (
      pf: !avltree_v (key, itm, h, slf)
    | p: ptr slf, res: &itm? >> opt (itm, b)
    ) :<cloref> #[b:bool] bool b =
    if p > null then let
      prval B (pf_at, pf_l, pf_r) = pf
      val sgn = compare_key_key (k0, avlnode_get_key<key,itm> (pf_at | p), cmp)
    in
      if sgn < 0 then let
        val tag = search (pf_l | avlnode_get_left<key,itm> (pf_at | p), res)
        prval () = pf := B (pf_at, pf_l, pf_r)
      in
        tag
      end else if sgn > 0 then let
        val tag = search (pf_r | avlnode_get_right<key,itm> (pf_at | p), res)
        prval () = pf := B (pf_at, pf_l, pf_r)
      in
        tag
      end else let
        val (
          pf1_at, fpf | p1
        ) = avlnode_takeout_val<key,itm> (pf_at | p)
        val () = res := !p1
        prval () = pf_at := fpf (pf1_at)
        prval () = opt_some {itm} (res) // [itm] is a t@ype
        prval () = pf := B (pf_at, pf_l, pf_r)
      in
        true // item associated with the key [k0] is found
      end // end of [if]
    end else let
      prval () = opt_none {itm} (res) in false
    end // end of [if]
  // end of [search]
} // end of [linmap_search]

(* ****** ****** *)

(*
** left rotation for restoring height invariant
*)
fn{key:t0p;itm:vt0p}
avltree_lrotate {h:int;hl,hr:nat | hl+HTDF1 == hr} {l_t:agz;l_tl,l_tr:addr} (
    pf_nod: avlnode_v (key, itm, h, l_tl, l_tr, l_t)
  , pf_tl: avltree_v (key, itm, hl, l_tl)
  , pf_tr: avltree_v (key, itm, hr, l_tr)
  | p: ptr l_t, hl: int hl, hr: int hr
  ) :<> [l:agz] (avltree_v_inc (key, itm, hr, l) | ptr l) = let
  val p_tl = avlnode_get_left<key,itm> (pf_nod | p)
  and p_tr = avlnode_get_right<key,itm> (pf_nod | p)
  prval B {..} {hrl,hrr} (pf_rnod, pf_trl, pf_trr) = pf_tr
  val p_trl = avlnode_get_left<key,itm> (pf_rnod | p_tr)
  and p_trr = avlnode_get_right<key,itm> (pf_rnod | p_tr)
  val hrl = avltree_height<key,itm> (pf_trl | p_trl)
  and hrr = avltree_height<key,itm> (pf_trr | p_trr)
in
  if hrl <= hrr+HTDF_1 then let
    val hrl1 = hrl + 1
    val () = avlnode_set_height<key,itm> (pf_nod | p, hrl1)
    val () = avlnode_set_right<key,itm> (pf_nod | p, p_trl)
    prval pf_t = B (pf_nod, pf_tl, pf_trl)
    val () = avlnode_set_height<key,itm> (pf_rnod | p_tr, 1+max(hrl1,hrr))
    val () = avlnode_set_left<key,itm> (pf_rnod | p_tr, p)
    prval pf_tr = B (pf_rnod, pf_t, pf_trr)
  in
    (pf_tr | p_tr) // B (1+max(hrl1,hrr), kr, xr, B (hrl1, k, x, tl, trl), trr)
  end else let // [hrl=hrr+2]: deep rotation
    prval B {..} {hrll,hrlr} (pf_rlnod, pf_trll, pf_trlr) = pf_trl
    val p_trll = avlnode_get_left<key,itm> (pf_rlnod | p_trl)
    and p_trlr = avlnode_get_right<key,itm> (pf_rlnod | p_trl)
    val hrll = avltree_height (pf_trll | p_trll)
    and hrlr = avltree_height (pf_trlr | p_trlr)
    val () = avlnode_set_height<key,itm> (pf_nod | p, 1+max(hl,hrll))
    val () = avlnode_set_right<key,itm> (pf_nod | p, p_trll)
    prval pf_t = B (pf_nod, pf_tl, pf_trll)
    val () = avlnode_set_height<key,itm> (pf_rnod | p_tr, 1+max(hrlr, hrr))
    val () = avlnode_set_left<key,itm> (pf_rnod | p_tr, p_trlr)
    prval pf_tr = B (pf_rnod, pf_trlr, pf_trr)
    val () = avlnode_set_height<key,itm> (pf_rlnod | p_trl, hr)
    val () = avlnode_set_left<key,itm> (pf_rlnod | p_trl, p)
    val () = avlnode_set_right<key,itm> (pf_rlnod | p_trl, p_tr)
    prval pf_trl = B (pf_rlnod, pf_t, pf_tr)
  in
    (pf_trl | p_trl) // B (hr, krl, xrl, B (1+max(hl,hrll), k, x, tl, trll), B (1+max(hrlr,hrr), kr, xr, trlr, trr))
  end // end of [if]
end // end of [avltree_lrotate]

(*
** right rotation for restoring height invariant
*)
fn{key:t0p;itm:vt0p}
avltree_rrotate {h:int;hl,hr:nat | hl==hr+HTDF1} {l_t:agz;l_tl,l_tr:addr} (
    pf_nod: avlnode_v (key, itm, h, l_tl, l_tr, l_t)
  , pf_tl: avltree_v (key, itm, hl, l_tl)
  , pf_tr: avltree_v (key, itm, hr, l_tr)
  | p: ptr l_t, hl: int hl, hr: int hr
  ) :<> [l:agz] (avltree_v_inc (key, itm, hl, l) | ptr l) = let
  val p_tl = avlnode_get_left<key,itm> (pf_nod | p)
  and p_tr = avlnode_get_right<key,itm> (pf_nod | p)
  prval B {..} {hll,hlr} (pf_lnod, pf_tll, pf_tlr) = pf_tl
  val p_tll = avlnode_get_left<key,itm> (pf_lnod | p_tl)
  and p_tlr = avlnode_get_right<key,itm> (pf_lnod | p_tl)
  val hll = avltree_height<key,itm> (pf_tll | p_tll)
  and hlr = avltree_height<key,itm> (pf_tlr | p_tlr)
in
  if hll+HTDF_1 >= hlr then let
    val hlr1 = hlr + 1
    val () = avlnode_set_height<key,itm> (pf_nod | p, hlr1)
    val () = avlnode_set_left<key,itm> (pf_nod | p, p_tlr)
    prval pf_t = B (pf_nod, pf_tlr, pf_tr)
    val () = avlnode_set_height<key,itm> (pf_lnod | p_tl, 1+max(hll,hlr1))
    val () = avlnode_set_right<key,itm> (pf_lnod | p_tl, p)
    prval pf_tl = B (pf_lnod, pf_tll, pf_t)
  in
    (pf_tl | p_tl) // B (1+max(hll,hlr1), kl, xl, tll, B (hlr1, k, x, tlr, tr))
  end else let
    prval B {..} {hlrl,hlrr} (pf_lrnod, pf_tlrl, pf_tlrr) = pf_tlr
    val p_tlrl = avlnode_get_left<key,itm> (pf_lrnod | p_tlr)
    and p_tlrr = avlnode_get_right<key,itm> (pf_lrnod | p_tlr)
    val hlrl = avltree_height (pf_tlrl | p_tlrl)
    val hlrr = avltree_height (pf_tlrr | p_tlrr)
    val () = avlnode_set_height<key,itm> (pf_nod | p, 1+max(hlrr,hr))
    val () = avlnode_set_left<key,itm> (pf_nod | p, p_tlrr)
    prval pf_t = B (pf_nod, pf_tlrr, pf_tr)
    val () = avlnode_set_height<key,itm> (pf_lnod | p_tl, 1+max(hll,hlrl))
    val () = avlnode_set_right<key,itm> (pf_lnod | p_tl, p_tlrl)
    prval pf_tl = B (pf_lnod, pf_tll, pf_tlrl)
    val () = avlnode_set_height<key,itm> (pf_lrnod | p_tlr, hl)
    val () = avlnode_set_left<key,itm> (pf_lrnod | p_tlr, p_tl)
    val () = avlnode_set_right<key,itm> (pf_lrnod | p_tlr, p)
    prval pf_tlr = B (pf_lrnod, pf_tl, pf_t)
  in
    (pf_tlr | p_tlr) // B (hl, klr, xlr, B (1+max(hll,hlrl), kl, xl, tll, tlrl), B (1+max(hlrr,hr), k, x, tlrr, tr))
  end // end of [if]
end // end of [avltree_rrotate]

(* ****** ****** *)

implement{key,itm}
linmap_insert {l} (pf_nod | m, p, cmp) = let
//
fun insert {l_at,l_t:addr} {h:nat} .<h>. (
  pf_t: !avltree_v (key, itm, h, l_t) >> avltree_v_inc (key, itm, h, l_t1)
, pf_at: !avlnode_v (key, itm, l_at) >> option_v (avlnode_v (key, itm, l_at1), b)
| p0: &ptr l_at >> ptr l_at1, p: &ptr l_t >> ptr l_t1, cmp: cmp key
) :<> #[b:bool;l_t1,l_at1:addr] bool b =
  if p > null then let
    prval B (pf1_at, pf_tl, pf_tr) = pf_t
    val sgn = compare_key_key
      (avlnode_get_key<key,itm> (pf_at | p0), avlnode_get_key<key,itm> (pf1_at | p), cmp)
    // end of [val]
    var p_tl = avlnode_get_left<key,itm> (pf1_at | p)
    and p_tr = avlnode_get_right<key,itm> (pf1_at | p)
  in
    if sgn < 0 then let
      val ans = insert (pf_tl, pf_at | p0, p_tl, cmp)
      val () = avlnode_set_left<key,itm> (pf1_at | p, p_tl)
      val hl = avltree_height<key,itm> (pf_tl | p_tl)
      and hr = avltree_height<key,itm> (pf_tr | p_tr)
    in
      if hl - hr <= HTDF then let
        val () = avlnode_set_height<key,itm> (pf1_at | p, 1+max(hl,hr))
        prval () = pf_t := B {key,itm} (pf1_at, pf_tl, pf_tr)
      in
        ans // B (1+max(hl,hr), k, x, tl, tr)
      end else let // hl = hr+HTDF1
        val (pf1 | p1) = avltree_rrotate<key,itm>
          (pf1_at, pf_tl, pf_tr | p, hl, hr)
        prval () = pf_t := pf1
        val () = p := p1
      in
        ans
      end // end of [if]
    end else if sgn > 0 then let
      val ans = insert (pf_tr, pf_at | p0, p_tr, cmp)
      val () = avlnode_set_right<key,itm> (pf1_at | p, p_tr)
      val hl = avltree_height<key,itm> (pf_tl | p_tl)
      and hr = avltree_height<key,itm> (pf_tr | p_tr)
    in
      if hr - hl <= HTDF then let
        val () = avlnode_set_height<key,itm> (pf1_at | p, 1+max(hl, hr))
        prval () = pf_t := B (pf1_at, pf_tl, pf_tr)
      in
        ans // B (1+max(hl, hr), k, x, tl, tr)
      end else let // hl+HTDF1 = hr
        val (pf1 | p1) = avltree_lrotate<key,itm>
          (pf1_at, pf_tl, pf_tr | p, hl, hr)
        prval () = pf_t := pf1
        val () = p := p1
      in
        ans
      end // end of [if]
    end else let (* key already exists *)
      // swap the two nodes
      val () = avlnode_set_height<key,itm> (pf_at | p0, avlnode_get_height<key,itm> (pf1_at | p))
      val () = avlnode_set_left<key,itm> (pf_at | p0, avlnode_get_left<key,itm> (pf1_at | p))
      val () = avlnode_set_right<key,itm> (pf_at | p0, avlnode_get_right<key,itm> (pf1_at | p))
      val tmp = p
      val () = p := p0
      val () = p0 := tmp
      prval () = avlnode_ptr_is_gtz (pf_at)
      prval () = pf_t := B (pf_at, pf_tl, pf_tr)
      prval () = pf_at := Some_v (pf1_at)
    in
      true // B (h, k, x0, tl, tr)
    end // end of [if]
  end else let
    // a new node is created
    prval E () = pf_t
    val () = avlnode_set_height<key,itm> (pf_at | p0, 1)
    val () = avlnode_set_left<key,itm> (pf_at | p0, null)
    val () = avlnode_set_right<key,itm> (pf_at | p0, null)
    prval () = avlnode_ptr_is_gtz (pf_at)
    prval () = pf_t := B {key,itm} (pf_at, E (), E ())
    val () = p := p0
    prval () = pf_at := None_v ()
  in
    false
  end // end of [if]
in
  insert (m.0, pf_nod | p, m.1, cmp)
end // end of [linmap_insert]

(* ****** ****** *)

fun{key:t0p;itm:vt0p}
avltree_takeout_min {h:pos} {l_t:addr} .<h>. (
  pf_t: !avltree_v (key, itm, h, l_t) >> avltree_v_dec (key, itm, h, l_t1)
| p_t: &ptr l_t >> ptr l_t1
) :<> #[l_t1:addr] [l:addr] (avlnode_v (key, itm, l) | ptr l) = let
  prval B (pf_nod, pf_tl, pf_tr) = pf_t
  var p_tl = avlnode_get_left<key,itm> (pf_nod | p_t)
  and p_tr = avlnode_get_right<key,itm> (pf_nod | p_t)
in
  if p_tl > null then let
    prval B (pf_lnod, pf_tll, pf_tlr) = pf_tl
    prval () = pf_tl := B (pf_lnod, pf_tll, pf_tlr)
    val (pf_at | p_at) = avltree_takeout_min<key,itm> (pf_tl | p_tl)
    val hl = avltree_height<key,itm> (pf_tl | p_tl)
    val hr = avltree_height<key,itm> (pf_tr | p_tr)
    val () = avlnode_set_left<key,itm> (pf_nod | p_t, p_tl)
  in
    if hr - hl <= HTDF then let
      val () = avlnode_set_height<key,itm> (pf_nod | p_t, 1+max(hl,hr))
      prval () = pf_t := B (pf_nod, pf_tl, pf_tr)
    in
      (pf_at | p_at)
    end else let
      val (pf_t1 | p_t1) = avltree_lrotate<key,itm>
        (pf_nod, pf_tl, pf_tr | p_t, hl, hr)
      // end of [val]
      val () = p_t := p_t1
      prval () = pf_t := pf_t1
    in
      (pf_at | p_at)
    end // end of [if]
  end else let
    prval E () = pf_tl
    prval () = pf_t := pf_tr
    val p_res = p_t
    val () = p_t := avlnode_get_right<key,itm> (pf_nod | p_t)
  in
    (pf_nod | p_res)
  end // end of [if]
end // end of [avltree_takeout_min]

(* ****** ****** *)

implement{key,itm}
linmap_takeout
  (m, k0, cmp) = takeout (m.0 | m.1) where {
  fun takeout {h:nat} {l0:addr} .<h>. (
    pf_t: !avltree_v (key, itm, h, l0) >> avltree_v_dec (key, itm, h, l1)
  | p_t: &ptr l0 >> ptr l1
  ) :<cloref> #[l1:addr] [l_at:addr] (
    option_v (avlnode_v (key, itm, l_at), l_at > null)
  | ptr l_at
  ) = begin
    if p_t > null then let
      prval B (pf_nod, pf_tl, pf_tr) = pf_t
      val sgn = compare_key_key (k0, avlnode_get_key<key,itm> (pf_nod | p_t), cmp)
      var p_tl = avlnode_get_left<key,itm> (pf_nod | p_t)
      and p_tr = avlnode_get_right<key,itm> (pf_nod | p_t)
    in
      case+ 0 of
      | _ when sgn < 0 => let
          val ans(*removed*) = takeout (pf_tl | p_tl)
          val () = avlnode_set_left<key,itm> (pf_nod | p_t, p_tl)
          val hl = avltree_height<key,itm> (pf_tl | p_tl)
          and hr = avltree_height<key,itm> (pf_tr | p_tr)
        in
          if hr - hl <= HTDF then let
            val () = avlnode_set_height<key,itm> (pf_nod | p_t, 1+max(hl,hr))
            prval () = pf_t := B (pf_nod, pf_tl, pf_tr)
          in
            ans
          end else let // hl+HTDF1 = hr
            val (pf_t1 | p_t1) = avltree_lrotate<key,itm>
                (pf_nod, pf_tl, pf_tr | p_t, hl, hr)
            val () = p_t := p_t1
            prval () = pf_t := pf_t1
          in
            ans
          end // end of [if]
        end // end of [sgn < 0]
      | _ when sgn > 0 => let
          val ans = takeout (pf_tr | p_tr)
          val () = avlnode_set_right<key,itm> (pf_nod | p_t, p_tr)
          val hl = avltree_height<key,itm> (pf_tl | p_tl)
          and hr = avltree_height<key,itm> (pf_tr | p_tr)
        in
          if hl - hr <= HTDF then let
            val () = avlnode_set_height<key,itm> (pf_nod | p_t, 1+max(hl,hr))
            prval () = pf_t := B (pf_nod, pf_tl, pf_tr)
          in
            ans
          end else let // hl=hr+HTDF1
            val (pf_t1 | p_t1) = avltree_rrotate<key,itm>
                (pf_nod, pf_tl, pf_tr | p_t, hl, hr)
            // end of [val]
            val () = p_t := p_t1
            prval () = pf_t := pf_t1
          in
            ans
          end // end of [if]
        end // end of [sgn > 0]
      | _ (*sgn = 0*) => let
          stavar l_res: addr
          val p_res = p_t: ptr l_res
          prval () = avlnode_ptr_is_gtz (pf_nod)
          prval pf_res = Some_v (pf_nod): option_v (avlnode_v (key, itm, l_res), l_res > null)
        in
          if p_tr > null then let
            prval B (pf1_nod, pf1_tl, pf1_tr) = pf_tr
            prval () = pf_tr := B (pf1_nod, pf1_tl, pf1_tr)
            val (pf_t1 | p_t1) = avltree_takeout_min<key,itm> (pf_tr | p_tr)
            prval () = avlnode_ptr_is_gtz (pf_t1)
            val hl = avltree_height<key,itm> (pf_tl | p_tl)
            and hr = avltree_height<key,itm> (pf_tr | p_tr)
            val () = avlnode_set_left<key,itm> (pf_t1 | p_t1, p_tl)
            val () = avlnode_set_right<key,itm> (pf_t1 | p_t1, p_tr)
          in
            if hl - hr <= HTDF then let
              val () = avlnode_set_height<key,itm> (pf_t1 | p_t1, 1+max(hl,hr))
              val () = p_t := p_t1
              prval () = pf_t := B {key,itm} (pf_t1, pf_tl, pf_tr)
            in
              (pf_res | p_res)
            end else let
              val (pf_t1 | p_t1) = avltree_rrotate<key,itm> (pf_t1, pf_tl, pf_tr | p_t1, hl, hr)
              prval () = pf_t := pf_t1
              val () = p_t := p_t1
            in
              (pf_res | p_res)
            end // end of [if]
          end else let
            prval E () = pf_tr
            val () = p_t := p_tl
            prval () = pf_t := pf_tl
          in
            (pf_res | p_res)
          end // end of [if]
        end // end of [sgn = 0]
      // end // end of [B]
    end else let
      prval E () = pf_t
      prval () = pf_t := E {key,itm} ()
      val () = p_t := null
      stavar l_res: addr
      val p_res = null: ptr l_res
      prval pf_res = None_v (): option_v (avlnode_v (key, itm, l_res), l_res > null)
    in
      (pf_res | p_res)
    end // end of [if]
  end // end of [takeout]
} // end of [linmap_takeout]

(* ****** ****** *)

implement{key,itm}
linmap_remove (m, k0, cmp) = let
  val (pf | p) = linmap_takeout<key,itm> (m, k0, cmp)
in
  if p > null then let
    prval Some_v (pf_nod) = pf
  in
    avlnode_free<key,itm> (pf_nod | p); true
  end else let
    prval None_v () = pf in false
  end // end of [if]
end // end of [linmap_remove]

(* ****** ****** *)

implement{key,itm}
linmap_foreach_funenv {v} {vt}
  (pf | m, f, env) =
  foreach (pf, m.0 | m.1, env) where {
//
fun foreach
  {h:nat} {l:addr} .<h>. (
  pfv: !v
, pf1: !avltree_v (key, itm, h, l)
| p_t: ptr l, env: !vt
) :<cloref> void =
  if p_t > null then let
    prval B (pf_nod, pf_tl, pf_tr) = pf1
    val k = avlnode_get_key<key,itm> (pf_nod | p_t)
    and p_tl = avlnode_get_left<key,itm> (pf_nod | p_t)
    and p_tr = avlnode_get_right<key,itm> (pf_nod | p_t)
    val () = foreach (pfv, pf_tl | p_tl, env)
    val (pf_at, fpf | p) = avlnode_takeout_val<key,itm> (pf_nod | p_t)
    val () = f (pfv | k, !p, env)
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
  {h:nat} {l:addr} .<h>. (
  pfv: !v
, pf1: !avltree_v (key, itm, h, l)
| p_t: ptr l
, f: &(!v | key, &itm) -<clo> void
) :<> void =
  if p_t > null then let
    prval B (pf_nod, pf_tl, pf_tr) = pf1
    val k = avlnode_get_key<key,itm> (pf_nod | p_t)
    and p_tl = avlnode_get_left<key,itm> (pf_nod | p_t)
    and p_tr = avlnode_get_right<key,itm> (pf_nod | p_t)
    val () = foreach (pfv, pf_tl | p_tl, f)
    val (pf_at, fpf | p) = avlnode_takeout_val<key,itm> (pf_nod | p_t)
    val () = f (pfv | k, !p)
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
  {h:nat} {l:addr} .<h>. (
  pfv: !v
, pf1: !avltree_v (key, itm, h, l)
| p_t: ptr l, env: !vt
) :<cloref> void =
  if p_t > null then let
    prval B (pf_nod, pf_tl, pf_tr) = pf1
    val k = avlnode_get_key<key,itm> (pf_nod | p_t)
    and p_tl = avlnode_get_left<key,itm> (pf_nod | p_t)
    and p_tr = avlnode_get_right<key,itm> (pf_nod | p_t)
    val () = rforeach (pfv, pf_tr | p_tr, env)
    val (pf_at, fpf | p) = avlnode_takeout_val<key,itm> (pf_nod | p_t)
    val () = f (pfv | k, !p, env)
    prval () = pf_nod := fpf {itm} (pf_at)
    val () = rforeach (pfv, pf_tl | p_tl, env)
    prval () = pf1 := B (pf_nod, pf_tl, pf_tr)
  in
    // nothing
  end else let
    prval E () = pf1; prval () = pf1 := E () in
    // nothing
  end // end of [if]
// end of [rforeach]
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
//
// HX: freeing is done in the inord fashion
//
fun _free
  {h:nat} {l:addr} .<h>. (
  pf1: avltree_v (key, itm, h, l) | p_t: ptr l
) :<cloref> void =
  if p_t > null then let
    prval B (pf_nod, pf_tl, pf_tr) = pf1
    val p_tl = avlnode_get_left<key,itm> (pf_nod | p_t)
    and p_tr = avlnode_get_right<key,itm> (pf_nod | p_t)
    val () = avlnode_free<key,itm> (pf_nod | p_t)
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

(* end of [linmap_avltree.dats] *)
