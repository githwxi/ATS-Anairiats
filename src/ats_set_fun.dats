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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2007

(* ****** ****** *)

typedef cmp_t (a:t@ype) = (a, a) -<fun> Sgn

(* ****** ****** *)

datatype avl (
  a:t@ype+, int (*height*), int (*size*)
) =
  | E (a, 0, 0)
  | {lh,ls,rh,rs:nat | rh <= lh; lh <= rh+1}
    Bl(a, 1+lh, 1+ls+rs) of (a, int(1+lh), avl (a, lh, ls), avl (a, rh, rs))
  | {lh,ls,rh,rs:nat | lh <= rh; rh <= lh+1}
    Br(a, 1+rh, 1+ls+rs) of (a, int(1+rh), avl (a, lh, ls),  avl (a, rh, rs))
// end of [avl]

typedef avl_dec (a:t@ype, h:int, s:int) = [h1:nat | h1 <= h; h <= h1+1] avl (a, h1, s)
typedef avl_inc (a:t@ype, h:int, s:int) = [h1:nat | h <= h1; h1 <= h+1] avl (a, h1, s)

typedef avl = [a:t@ype] [h,s:int] avl (a, h, s)

(* ****** ****** *)

extern fun{a:t@ype} avl_size {h,s:nat} (t: avl (a, h, s)): int s

implement{a} avl_size (t) = case+ t of
  | Bl (_, _, l, r) => 1 + (avl_size l + avl_size r)
  | Br (_, _, l, r) => 1 + (avl_size l + avl_size r)
  | E () => 0
// end of [avl_size]

extern fun{a:t@ype} avl_height {h,s:nat} (t: avl (a, h, s)): int h

implement{a} avl_height (t) = case+ t of
  | E () => 0 | Bl (_, h, _, _) => h | Br (_, h, _, _) => h
// end of [avl_height]

(* ****** ****** *)

extern fun{a:t@ype} avl_member
  {h,s:nat} (t: avl (a, h, s), e0: a, cmp: cmp_t a): bool

implement{a} avl_member (t, e0, cmp) = begin
  case+ t of
  | Bl (e, _, l, r) => begin case+ cmp (e0, e) of
    | ~1 => avl_member (l, e0, cmp)
    |  1 => avl_member (r, e0, cmp)
    |  0 => true
    end // end of [Bl]
  | Br (e, _, l, r) => begin case+ cmp (e0, e) of
    | ~1 => avl_member (l, e0, cmp)
    |  1 => avl_member (r, e0, cmp)
    |  0 => true
    end // end of [Br]
  | E () => false
end // end of [avl_member]

extern fun{a:t@ype} avl_search
  {h,s:nat} (t: avl (a, h, s), pred: !a -<cloptr1> Sgn): Option a

implement{a} avl_search (t, pred) = begin
  case+ t of
  | Bl (e, _, l, r) => begin case+ pred e of
    | ~1 => avl_search (l, pred)
    |  1 => avl_search (r, pred)
    |  0 => Some e
    end // end of [Bl]
  | Br (e, _, l, r) => begin case+ pred e of
    | ~1 => avl_search (l, pred)
    |  1 => avl_search (r, pred)
    |  0 => Some e
    end // end of [Br]
  | E () => None ()
end // end of [avl_search]

extern fun{a:t@ype} avl_foreach {v:view} {vt:viewtype} {h,s:nat} {f:eff}
  (pf: !v | t: avl (a, h, s), f: (!v | a, !vt) -<f> void, env: !vt):<f> void

implement{a} avl_foreach (pf | t, f, env) = begin case+ t of
  | Bl (e, _, l, r) => begin
      avl_foreach (pf | l, f, env); f (pf | e, env); avl_foreach (pf | r, f, env)
    end // end of [Bl]
  | Br (e, _, l, r) => begin
      avl_foreach (pf | l, f, env); f (pf | e, env); avl_foreach (pf | r, f, env)
    end // end of [Br]
  | E () => ()
end // end of [avl_foreach]

(* ****** ****** *)

extern fun{a:t@ype} avl_rotate_l {ls,rh,rs:nat}
  (e: a, l: avl (a, rh+2, ls), r: avl (a, rh, rs)): avl_inc (a, rh+2, 1+ls+rs)

implement{a} avl_rotate_l (e, l, r) = begin
  case+ l of
  | Bl (le, lh, ll, lr) => let
      val lrh = avl_height (lr)
    in
      Br (le, lrh+2, ll, Bl (e, lrh+1, lr, r))
    end // end of [Bl]
  | Br (le, lh, ll, lr) => let
      val llh = avl_height ll and lrh = avl_height lr
    in
      if llh < lrh then begin case+ lr of // rh = llh: deep rotation
        | Bl (lre, _, lrl, lrr) =>
            Br (lre, lh, Bl (le, llh+1, ll, lrl), Br (e, lh-1, lrr, r))
        | Br (lre, _, lrl, lrr) =>
            Br (lre, lh, Bl (le, llh+1, ll, lrl), Br (e, lh-1, lrr, r))
      end else begin
        Br (le, lrh+2, ll, Bl (e, lrh+1, lr, r))
      end // end of [if]
    end // end of [Br]
end // end of [avl_rotate_l]

extern fun{a:t@ype} avl_rotate_r {lh,ls,rs:nat}
  (e: a, l: avl (a, lh, ls), r: avl (a, lh+2, rs)): avl_inc (a, lh+2, 1+ls+rs)

implement{a} avl_rotate_r (e, l, r) = begin
  case+ r of
  | Bl (re, rh, rl, rr) => let
      val rlh = avl_height rl and rrh = avl_height rr
    in
      if rlh > rrh then begin case+ rl of // lh = rrh: deep rotation
        | Bl (rle, _, rll, rlr) =>
            Bl (rle, rh, Bl (e, rh-1, l, rll), Br (re, rrh+1, rlr, rr))
        | Br (rle, _, rll, rlr) =>
            Bl (rle, rh, Bl (e, rh-1, l, rll), Br (re, rrh+1, rlr, rr))
      end else begin
        Bl (re, rlh+2, Br (e, rlh+1, l, rl), rr)
      end
    end // end of [Bl]
  | Br (re, rh, rl, rr) => let
      val rlh = avl_height (rl)
    in
      Bl (re, rlh+2, Br (e, rlh+1, l, rl), rr)
    end // end of [Br]
end // end of [avl_rotate_r]

(* ****** ****** *)

extern fun{a:t@ype} avl_insert {h,s:nat}
  (t: avl (a, h, s), ne: a, cmp: cmp_t a)
  : [s',h': nat | s <= s'; s' <= s+1; h <= h'; h' <= h+1] avl (a, h', s')

extern fun{a:t@ype} avl_insert_br
  {h,lh,ls,rh,rs:nat | lh-1 <= rh; rh <= lh+1; max_r(lh, rh, h-1)}
  (e: a, h: int h, l: avl (a,lh,ls), r: avl (a,rh,rs), ne: a, cmp: cmp_t a)
  : [s:int | ls+rs+1 <= s; s <= ls+rs+2] avl_inc (a, h, s)

implement{a} avl_insert (t, ne, cmp) = begin case+ t of
  | E () => Bl (ne, 1, E (), E ())
  | Bl (e, h, l, r) => avl_insert_br (e, h, l, r, ne, cmp)
  | Br (e, h, l, r) => avl_insert_br (e, h, l, r, ne, cmp)
end // end of [avl_insert]

implement{a} avl_insert_br
  (e, h, l, r, ne, cmp) = let
  val sgn = cmp (ne, e)
in
  if sgn < 0 then let
    val l' = avl_insert<a> (l, ne, cmp)
    val lh' = avl_height l' and rh = avl_height r
  in
    if lh' <= rh then Br (e, rh+1, l', r)
    else if lh' <= rh+1 then Bl (e, lh'+1, l', r)
    else avl_rotate_l (e, l', r)
  end else if sgn > 0 then let
    val r' = avl_insert<a> (r, ne, cmp)
    val lh = avl_height l and rh' = avl_height r'
  in
    if rh' <= lh then Bl (e, lh+1, l, r')
    else if rh' <= lh + 1 then Br (e, rh'+1, l, r')
    else avl_rotate_r (e, l, r')
  end else let
    val lh = avl_height l and rh = avl_height r
  in
    if lh >= rh then Bl (e, h, l, r) else Br (e, h, l, r)
  end // end of [if]
end // end of [avl_insert_br]

(* ****** ****** *)

extern fun{a:t@ype} avl_takeout_min {h,s:nat | s > 0}
  (t: avl (a, h, s), x: &(a?) >> a): avl_dec (a, h, s-1)

implement{a} avl_takeout_min (t, x) = begin
  case+ : (x: a) => t of
  | Bl (e, _, l, r) => begin case+ : (x: a) => l of
    | E () => (x := e; r)
    | _ =>> let
        val l' = avl_takeout_min<a> (l, x)
        val lh' = avl_height l' and rh = avl_height r
      in
        if rh <= lh' then Bl (e, lh'+1, l', r) else Br (e, rh+1, l', r)
      end // end of [_]
    end // end of [Bl]
  | Br (e, _, l, r) => begin case+ : (x: a) => l of
    | E () => (x := e; r)
    | _ =>> let
        val l' = avl_takeout_min<a> (l, x)
        val lh' = avl_height l' and rh = avl_height r
      in
        if rh <= lh' then Bl (e, lh'+1, l', r)
        else if rh <= lh'+1 then Br (e, rh+1, l', r)
        else avl_rotate_r (e, l', r)
      end // end of [_]
    end // end of [Br]
end // end of [avl_takeout_min]

(* ****** ****** *)

extern fun{a:t@ype} avl_join_l {lh,ls,rh,rs:nat | lh >= rh}
  (e: a, l: avl (a, lh, ls), r: avl (a, rh, rs)): avl_inc (a, lh, 1+ls+rs)

implement{a} avl_join_l (e, l, r) = let
  val lh = avl_height l and rh = avl_height r
in
  if lh > rh+1 then begin case+ l of
    | Bl (le, _, ll, lr) => let
        val lr' = avl_join_l<a> (e, lr, r)
        val llh = avl_height ll and lrh' = avl_height lr'
      in
        if lrh' <= llh then Bl (le, llh+1, ll, lr')
        else Br (le, lrh'+1, ll, lr')
      end // end of [Bl]
    | Br (le, _, ll, lr) => let
        val lr' = avl_join_l<a> (e, lr, r)
        val llh = avl_height ll and lrh' = avl_height lr'
      in
        if lrh' <= llh+1 then Br (le, lrh'+1, ll, lr')
        else avl_rotate_r (le, ll, lr')
      end // end of [Br]
  end else begin
    Bl (e, lh+1, l, r)
  end // end of [if]
end // end of [avl_join_l]

extern fun{a:t@ype} avl_join_r {lh,ls,rh,rs:nat | lh <= rh}
  (e: a, l: avl (a, lh, ls), r: avl (a, rh, rs)): avl_inc (a, rh, 1+ls+rs)

implement{a} avl_join_r (e, l, r) = let
  val lh = avl_height l and rh = avl_height r
in
  if lh+1 < rh then begin case+ r of
    | Bl (re, _, rl, rr) =>  let
        val rl' = avl_join_r<a> (e, l, rl)
        val rlh' = avl_height rl' and rrh = avl_height rr
      in
        if rlh' <= rrh+1 then Bl (re, rlh'+1, rl', rr)
        else avl_rotate_l (re, rl', rr)
      end // end of [Bl]
    | Br (re, _, rl, rr) => let
        val rl' = avl_join_r<a> (e, l, rl)
        val rlh' = avl_height rl' and rrh = avl_height rr
      in
        if rlh' <= rrh then Br (re, rrh+1, rl', rr)
        else Bl (re, rlh'+1, rl', rr)
      end // end of [Br]
   end else begin
     Br (e, rh+1, l, r)
   end // end of [if]
end // end of [avl_join_r]

(* ****** ****** *)

extern fun{a:t@ype} avl_concat {h1,s1,h2,s2:nat}
  (t1: avl (a, h1, s1), t2: avl (a, h2, s2)): [h:nat] avl (a, h, s1+s2)

implement{a} avl_concat (t1, t2) = begin
  case+ (t1, t2) of
  | (E (), _) => t2
  | (_, E ()) => t1
  | (_, _) =>> let
      var x: a
      val t2 = avl_takeout_min<a> (t2, x)
      val h1 = avl_height t1 and h2 = avl_height t2
    in
      if h1 <= h2 then avl_join_r (x, t1, t2) else avl_join_l (x, t1, t2)
    end // end of [_, _]
end // end of [avl_concat]

(* ****** ****** *)

viewtypedef avl_split_vt
  (a:t@ype, h:int, s:int, lp: addr, rp: addr) =
  [lh,ls,rh,rs:nat; b:two | lh <= h; rh <= h; s==b+ls+rs]
    (avl (a, lh, ls) @ lp, avl (a, rh, rs) @ rp | int b)

extern fun{a:t@ype} avl_split {h,s:nat} {lp,rp:addr}
  (lpf: avl? @ lp, rpf: avl? @ rp |
   t: avl (a, h, s), pred: !a -<cloptr1> Sgn, lp: ptr lp, rp: ptr rp)
  : avl_split_vt (a, h, s, lp, rp)

extern fun{a:t@ype} avl_split_br
  {h,lh,ls,rh,rs:nat | lh-1 <= rh; rh <= lh+1; max_r(lh, rh, h-1)}
  {lp,rp:addr}
  (lpf: avl? @ lp, rpf: avl? @ rp |
   e: a, h: int h, l: avl (a, lh, ls), r: avl (a, rh, rs), pred: !a -<cloptr1> Sgn,
   lp: ptr lp, rp: ptr rp)
  : avl_split_vt (a, h, ls+rs+1, lp, rp)

implement{a} avl_split (lpf, rpf | t, pred, lp, rp) = case+ t of
  | Bl (e, h, l, r) => avl_split_br (lpf, rpf | e, h, l, r, pred, lp, rp)
  | Br (e, h, l, r) => avl_split_br (lpf, rpf | e, h, l, r, pred, lp, rp)
  | E () => begin
      !lp := E (); !rp := E (); (lpf, rpf | 0)
    end // end of [E]
// end of [avl_split]

implement{a} avl_split_br
  (lpf, rpf | e, h, l, r, pred, lp, rp) = begin
  case+ pred e of
  | ~1 => let
      val (lpf, rpf | tag) = avl_split (lpf, rpf | l, pred, lp, rp)
      val lrh' = avl_height !rp and rh = avl_height r
    in
      if lrh' <= rh then begin
        !rp := avl_join_r<a> (e, !rp, r); (lpf, rpf | tag)
      end else begin
        !rp := avl_join_l<a> (e, !rp, r); (lpf, rpf | tag)
      end // end of [if]
    end // end of [~]
  | 1 => let
      val (lpf, rpf | tag) = avl_split (lpf, rpf | r, pred, lp, rp)
      val lh = avl_height l and rlh' = avl_height !lp
    in
      if lh <= rlh' then begin
        !lp := avl_join_r<a> (e, l, !lp); (lpf, rpf | tag)
      end else begin
        !lp := avl_join_l<a> (e, l, !lp); (lpf, rpf | tag)
      end // end of [ 1]
    end // end of [if]
  | 0 => begin
      !lp := l; !rp := r; (lpf, rpf | 1)
    end // end of [0]
end // end of [avl_split_br]

(* ****** ****** *)

// difference operation

extern fun{a:t@ype} avl_diff {h1,s1,h2,s2:nat}
  (t1: avl (a, h1, s1), t2: avl (a, h2, s2), cmp: cmp_t a)
  : [h,s:nat | s <= s1] avl (a, h, s)

extern fun{a:t@ype} avl_diff_br
  {h1,lh1,ls1,rh1,rs1,h2,s2:nat |
   lh1-1 <= rh1; rh1 <= lh1+1; max_r(lh1, rh1, h1-1)}
  (e1: a, h1: int h1, l1: avl (a, lh1, ls1), r1: avl (a, rh1, rs1), 
   t2: avl (a, h2, s2), cmp: cmp_t a)
  : [h,s:nat | s <= 1+ls1+rs1] avl (a, h, s)

implement{a} avl_diff (t1, t2, cmp) = begin
  case+ (t1, t2) of
  | (E (), _) => E ()
  | (_, E ()) => t1
  | (Bl (e1, h1, l1, r1), _) => avl_diff_br (e1, h1, l1, r1, t2, cmp)
  | (Br (e1, h1, l1, r1), _) => avl_diff_br (e1, h1, l1, r1, t2, cmp)
end // end of [avl_diff]

implement{a} avl_diff_br (e1, h1, l1, r1, t2, cmp) = let
  var l2: avl? and r2: avl?
  val pred = lam (e2: a): Sgn =<cloptr1> cmp (e1, e2)
  val (lpf, rpf | tag) =
    avl_split (view@ l2, view@ r2 | t2, pred, &l2, &r2)
  val () = cloptr_free (pred)
  prval () = (view@ l2 := lpf; view@ r2 := rpf)
  val l = avl_diff (l1, l2, cmp) and r = avl_diff (r1, r2, cmp)
  val lh = avl_height l and rh = avl_height r
in
  if tag > 0 then avl_concat<a> (l, r)
  else if lh <= rh then avl_join_r<a> (e1, l, r)
  else avl_join_l<a> (e1, l, r)
end // end of [avl_diff_br]

(* ****** ****** *)

// intersection operation

extern fun{a:t@ype} avl_inter {h1,s1,h2,s2:nat}
  (t1: avl (a, h1, s1), t2: avl (a, h2, s2), cmp: cmp_t a)
  : [h,s:nat | s <= s1; s <= s2] avl (a, h, s)

extern fun{a:t@ype} avl_inter_br
  {h1,lh1,ls1,rh1,rs1,h2,s2:nat |
   lh1-1 <= rh1; rh1 <= lh1+1; max_r(lh1, rh1, h1-1)}
  (e1: a, h1: int h1, l1: avl (a, lh1, ls1), r1: avl (a, rh1, rs1), 
   t2: avl (a, h2, s2), cmp: cmp_t a)
  : [h,s:nat | s <= ls1+rs1+1; s <= s2] avl (a, h, s)

implement{a} avl_inter (t1, t2, cmp) = begin
  case+ (t1, t2) of
  | (E (), _) => E ()
  | (_, E ()) => E ()
  | (Bl (e1, h1, l1, r1), _) => avl_inter_br (e1, h1, l1, r1, t2, cmp)
  | (Br (e1, h1, l1, r1), _) => avl_inter_br (e1, h1, l1, r1, t2, cmp)
end // end of [avl_inter]

implement{a} avl_inter_br (e1, h1, l1, r1, t2, cmp) = let
  var l2: avl? and r2: avl?
  val pred = lam (e2: a): Sgn =<cloptr1> cmp (e1, e2)
  val (lpf, rpf | tag) =
    avl_split (view@ l2, view@ r2 | t2, pred, &l2, &r2)
  val () = cloptr_free (pred)
  prval () = (view@ l2 := lpf; view@ r2 := rpf)
  val l = avl_inter (l1, l2, cmp) and r = avl_inter (r1, r2, cmp)
  val lh = avl_height l and rh = avl_height r
in
  if tag > 0 then
    if lh <= rh then avl_join_r<a> (e1, l, r) else avl_join_l<a> (e1, l, r)
  else avl_concat<a> (l, r)
end // end of [avl_inter_br]

(* ****** ****** *)

extern fun{a:t@ype} avl_union {h1,s1,h2,s2:nat}
  (t1: avl (a, h1, s1), t2: avl (a, h2, s2), cmp: cmp_t a)
  : [h,s:nat | s1 <= s; s2 <= s; s <= s1+s2] avl (a, h, s)

extern fun{a:t@ype} avl_union_br
  {h1,lh1,ls1,rh1,rs1,h2,s2:nat |
   lh1-1 <= rh1; rh1 <= lh1+1; max_r(lh1, rh1, h1-1)}
  (e1: a, h1: int h1, l1: avl (a, lh1, ls1), r1: avl (a, rh1, rs1), 
   t2: avl (a, h2, s2), cmp: cmp_t a)
  : [h,s:nat | 1+ls1+rs1 <= s; s2 <= s; s <= 1+ls1+rs1+s2] avl (a, h, s)

implement{a} avl_union (t1, t2, cmp) = case+ (t1, t2) of
  | (E (), _) => t2
  | (_, E ()) => t1
  | (Bl (e1, h1, l1, r1), _) => avl_union_br (e1, h1, l1, r1, t2, cmp)
  | (Br (e1, h1, l1, r1), _) => avl_union_br (e1, h1, l1, r1, t2, cmp)

implement{a} avl_union_br (e1, h1, l1, r1, t2, cmp) = let
  var l2: avl? and r2: avl?
  val pred = lam (e2: a): Sgn =<cloptr1> cmp (e1, e2)
  val (lpf, rpf | _) =
    avl_split (view@ l2, view@ r2 | t2, pred, &l2, &r2)
  val () = cloptr_free (pred)
  prval () = (view@ l2 := lpf; view@ r2 := rpf)
  val l = avl_union (l1, l2, cmp) and r = avl_union (r1, r2, cmp)
  val lh = avl_height l and rh = avl_height r
in
  if lh <= rh then avl_join_r<a> (e1, l, r) else avl_join_l<a> (e1, l, r)
end // end of [avl_union_br]

(* ****** ****** *)

// removal operation

extern fun{a:t@ype} avl_remove {h,s:nat}
  (t: avl (a, h, s), e0: a, cmp: cmp_t a): [s1:nat | s1 <= s] avl_dec (a, h, s1)

implement{a} avl_remove (t, e0, cmp) = begin case+ t of
  | E () => E ()
  | Bl (e, _, l, r) => begin case+ cmp (e0, e) of
    | ~1 => let
        val l' = avl_remove<a> (l, e0, cmp)
        val lh' = avl_height l' and rh = avl_height r
      in
        if rh <= lh' then Bl (e, lh'+1, l', r) else Br (e, rh+1, l', r)
      end // end of [~1]
    | 1 => let
        val r' = avl_remove<a> (r, e0, cmp)
        val lh = avl_height l and rh' = avl_height r'
      in
        if lh <= rh'+1 then Bl (e, lh+1, l, r') else avl_rotate_l (e, l, r')
      end // end of [1]
    | 0 => begin case+ r of
      | E () => l
      | _ =>> let
          var x: a; val r' = avl_takeout_min<a> (r, x)
          val lh = avl_height l and rh' = avl_height r'
        in
          if lh <= rh'+1 then Bl (x, lh+1, l, r') else avl_rotate_l (x, l, r')
        end
      end // end of [0]
    end // end of [Bl]
  | Br (e, _, l, r) => begin case+ cmp (e0, e) of
    | ~1 => let
        val l' = avl_remove<a> (l, e0, cmp)
        val lh' = avl_height l' and rh = avl_height r
      in
        if rh <= lh'+1 then Br (e, rh+1, l', r) else avl_rotate_r (e, l', r)
      end // end of [~1]
    | 1 => let
        val r' = avl_remove<a> (r, e0, cmp)
        val lh = avl_height l and rh' = avl_height r'
      in
        if rh' <= lh then Bl (e, lh+1, l, r') else Br (e, rh'+1, l, r')
      end // end of [1]
    | 0 => begin case+ r of
      | E () => l
      | _ =>> let
          var x: a; val r' = avl_takeout_min<a> (r, x)
          val lh = avl_height l and rh' = avl_height r'
        in
          if rh' <= lh then Bl (x, lh+1, l, r') else Br (x, rh'+1, l, r')
        end
      end  // end of [0]
    end // end of [Br]
end // end of [avl_remove]

(* ****** ****** *)

staload "ats_set_fun.sats"

assume set_t (a: t@ype) = [h,s:nat] avl (a, h, s)

implement set_nil = E ()
implement{a} set_member (xs, x, cmp) = avl_member (xs, x, cmp)
implement{a} set_insert (xs, x, cmp) = avl_insert (xs, x, cmp)
implement{a} set_remove (xs, x, cmp) = avl_remove (xs, x, cmp)
implement{a} set_inter (xs1, xs2, cmp) = avl_inter (xs1, xs2, cmp)
implement{a} set_union (xs1, xs2, cmp) = avl_union (xs1, xs2, cmp)

(* ****** ****** *)

implement{a} set_foreach_main (pf | xs, f, env) =
  avl_foreach<a> (pf | xs, f, env)

implement{a} set_foreach_cloptr {f:eff} (xs, f) = let
  viewtypedef cloptr_t = a -<cloptr,f> void
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = avl_foreach<a> {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [set_foreach_cloptr]

(* ****** ****** *)

(* end of [ats_set_fun.dats] *)
