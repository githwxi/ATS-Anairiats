(*
**
** An implementation of functional msets based on AVL trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

abstype mset_t (elt: t@ype)

(* ****** ****** *)

typedef cmp (elt:t@ype) = (elt, elt) -<cloref> Sgn

extern fun{elt:t@ype}
  compare_elt_elt (x1: elt, x2: elt, cmp: cmp elt):<> Sgn

implement{elt} compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

typedef cnt = [i:int | i > 0] int i (* positive integers *)

extern fun{} funmset_empty {elt:t@ype} ():<> mset_t (elt)

extern fun{elt:t@ype} funmset_singleton (x: elt):<> mset_t (elt)

extern fun{elt:t@ype} funmset_size (xs: mset_t elt):<> Nat

extern fun{elt:t@ype} funmset_member
  (xs: mset_t elt, x0: elt, cmp: cmp elt):<> Nat

extern fun{elt:t@ype} funmset_is_member
  (xs: mset_t elt, x0: elt, cmp: cmp elt):<> bool

extern fun{elt:t@ype} funmset_isnot_member
  (xs: mset_t elt, x0: elt, cmp: cmp elt):<> bool

extern fun{elt:t@ype} funmset_insert
  (xs: mset_t elt, x0: elt, cmp: cmp elt):<> mset_t (elt)

extern fun{elt:t@ype} funmset_remove
  (xs: mset_t elt, x0: elt, cmp: cmp elt):<> mset_t elt

extern fun{elt:t@ype} funmset_union
  (xs1: mset_t elt, xs2: mset_t elt, cmp: cmp elt):<> mset_t (elt)

extern fun{elt:t@ype} funmset_intersect
  (xs1: mset_t elt, xs2: mset_t elt, cmp: cmp elt):<> mset_t (elt)

extern fun{elt:t@ype} funmset_diff
  (xs1: mset_t elt, xs2: mset_t elt, cmp: cmp elt):<> mset_t (elt)

extern fun{elt:t@ype} funmset_foreach_clo {v:view}
  (pf: !v | xs: mset_t elt, f: &(!v | elt, cnt) -<clo> void):<> void

extern fun{elt:t@ype} funmset_foreach_cloref
  (xs: mset_t elt, f: (elt, cnt) -<cloref> void):<!ref> void

(* ****** ****** *)

datatype avltree (elt:t@ype+, int(*height*)) =
  | {hl,hr:nat | hl <= hr+1; hr <= hl+1}
    B (elt, max(hl,hr)+1) of
      (int (max(hl,hr)+1), elt, cnt, avltree (elt, hl), avltree (elt, hr))
  | E (elt, 0)

typedef avltree_inc (elt:t@ype, h:int) =
  [h1:nat | h <= h1; h1 <= h+1] avltree (elt, h1)

typedef avltree_dec (elt:t@ype, h:int) =
  [h1:nat | h1 <= h; h <= h1+1] avltree (elt, h1)

(* ****** ****** *)

assume mset_t (elt:t@ype) = [h:nat] avltree (elt, h)

(* ****** ****** *)

implement{} funmset_empty () = E ()
implement{elt} funmset_singleton (x) = B (1, x, 1, E (), E ())

(* ****** ****** *)

implement{elt} funmset_size (t) = size (t) where {
  fun size {h:nat} .<h>.
    (t: avltree (elt, h)):<> Nat = begin case+ t of
    | B (_(*h*), _(*x*), n, tl, tr) => n + size (tl) + size (tr)
    | E () => 0
  end // end of [size]
} // end of [funmset_size]

(* ****** ****** *)

implement{elt} funmset_member (t, x0, cmp) = mem (t) where {
  fun mem {h:nat} .<h>.
    (t: avltree (elt, h)):<cloref> Nat = case+ t of
    | B (_(*h*), x, n, tl, tr) => let
        val sgn = compare_elt_elt<elt> (x0, x, cmp)
      in
        if sgn < 0 then mem tl else if sgn > 0 then mem tr else n
      end // end of [B]
    | E () => 0
} // end of [funmset_member]

(* ****** ****** *)

implement{elt} funmset_is_member (t, x0, cmp) =
  if funmset_member<elt> (t, x0, cmp) > 0 then true else false
// end of [funmset_is_member]

implement{elt} funmset_isnot_member (t, x0, cmp) =
  if funmset_member<elt> (t, x0, cmp) > 0 then false else true
// end of [funmset_isnot_member]

(* ****** ****** *)

fn{elt:t@ype} avltree_height {h:nat}
  (t: avltree (elt, h)):<> int h = begin
  case+ t of | B (h, _, _, _, _) => h | E () => 0
end // end of [avltree_height]

(*
** left rotation for restoring height invariant
*)
fn{elt:t@ype} avltree_lrotate {hl,hr:nat | hl+2 == hr} (
    x: elt, n: cnt, tl: avltree (elt, hl), tr: avltree (elt, hr)
  ) :<> [h:nat | hr <= h; h <= hr+1] avltree (elt, h) = let
  val+ B (hr, xr, nr, trl, trr) = tr
  val hrl = avltree_height trl and hrr = avltree_height trr
in
  if hrl <= hrr then begin // hr = 1+hrr
    B (hrl+2, xr, nr, B (hrl+1, x, n, tl, trl), trr)
  end else let // [hrl > hrr]: deep rotation
    val+ B (_(*hrl*), xrl, nrl, trll, trlr) = trl
  in
    B (hr, xrl, nrl, B (hrl, x, n, tl, trll), B (hrl, xr, nr, trlr, trr))
  end // end of [if]
end // end of [avltree_lrotate]

(*
** right rotation for restoring height invariant
*)
fn{elt:t@ype} avltree_rrotate {hl,hr:nat | hl == hr+2} (
    x: elt, n: cnt, tl: avltree (elt, hl), tr: avltree (elt, hr)
  ) :<> [h:nat | hl <= h; h <= hl+1] avltree (elt, h) = let
  val+ B (hl, xl, nl, tll, tlr) = tl
  val hll = avltree_height tll and hlr = avltree_height tlr
in
  if hll >= hlr then begin // hl = 1+hll
    B (hlr+2, xl, nl, tll, B (hlr+1, x, n, tlr, tr))
  end else let // [hll < hlr]: deep rotation
    val+ B (_(*hlr*), xlr, nlr, tlrl, tlrr) = tlr
  in
    B (hl, xlr, nlr, B (hlr, xl, nl, tll, tlrl), B (hlr, x, n, tlrr, tr))
  end // end of [if]
end // end of [avltree_rrotate]

(* ****** ****** *)

implement{elt} funmset_insert (t, x0, cmp) = insert (t) where {
  fun insert {h:nat} .<h>.
    (t: avltree (elt, h)):<cloref> avltree_inc (elt, h) = case+ t of
    | B (h, x, n, tl, tr) => let
        val sgn = compare_elt_elt<elt> (x0, x, cmp)
      in
        if sgn < 0 then let
          val tl = insert (tl)
          val hl = avltree_height (tl) and hr = avltree_height (tr)
        in
          if hl - hr <= 1 then begin
            B (max(hl, hr) + 1, x, n, tl, tr)
          end else begin // hl = hr+2
            avltree_rrotate (x, n, tl, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val tr = insert (tr)
          val hl = avltree_height (tl) and hr = avltree_height (tr)
        in
          if hr - hl <= 1 then begin
            B (max(hl, hr)+1, x, n, tl, tr)
          end else begin // hl+1 = hr
            avltree_lrotate (x, n, tl, tr)
          end // end of [if]
        end else begin
          B (h, x, n+1, tl, tr)
        end // end of [if]
      end // end of [B]
    | E () => B (1, x0, 1, E (), E ())
} // end of [funmset_insert]

(* ****** ****** *)

fun{elt:t@ype} avltree_takeout_min {h:pos} .<h>. (
    t: avltree (elt, h)
  , x0: &elt? >> elt
  , n0: &cnt? >> cnt
  ) :<> avltree_dec (elt, h) = let
  val+ B (_, x, n, tl, tr) = t
in
  case+ tl of
  | B _ => let
      val tl = avltree_takeout_min<elt> (tl, x0, n0)
      val hl = avltree_height (tl) and hr = avltree_height (tr)
    in
      if hr - hl <= 1 then begin
        B (max(hl,hr)+1, x, n, tl, tr)
      end else begin // hl+2 = hr
       avltree_lrotate (x, n, tl, tr)
      end // end of [if]
    end // end of [B]
  | E () => (x0 := x; n0 := n; tr)
end // end of [avltree_takeout_min]

(* ****** ****** *)

implement{elt} funmset_remove (t, x0, cmp) = let
  fun remove {h:nat} .<h>.
    (t: avltree (elt, h), removed: &int? >> int i)
    :<cloref> #[i:two] avltree_dec (elt, h) =
    case+ t of
    | B (h, x, n, tl, tr) => let
        val sgn = compare_elt_elt<elt> (x0, x, cmp)
      in
        if sgn < 0 then let
          val tl = remove (tl, removed)
          val hl = avltree_height tl and hr = avltree_height tr
        in
          if hr - hl <= 1 then begin
            B (max(hl,hr)+1, x, n, tl, tr)
          end else begin // hl+2 == hr
            avltree_lrotate (x, n, tl, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val tr = remove (tr, removed)
          val hl = avltree_height tl and hr = avltree_height tr
        in
          if hl - hr <= 1 then begin
            B (max(hl,hr)+1, x, n, tl, tr)
          end else begin // hl = hr+2
            avltree_rrotate (x, n, tl, tr)
          end // end of [if]
        end else let
          val () = removed := 1
        in
          case+ 0 of
          | _ when n > 1  => B (h, x, n-1, tl, tr)
          | _ (* n = 1 *) => begin case+ tr of
            | B _ => let
                var x_min: elt and n_min: cnt
                val tr = avltree_takeout_min<elt> (tr, x_min, n_min)
                val hl = avltree_height tl and hr = avltree_height tr
              in
                if hl - hr <= 1 then begin
                  B (max(hl,hr)+1, x_min, n_min, tl, tr)
                end else begin // hl+2 = hr
                  avltree_rrotate (x_min, n_min, tl, tr)
                end // end of [if]
              end // end of [B]
            | E () => tl
          end // end of [_]
        end // end of [if]
      end // end of [B]
    | E () => (removed := 0; E ())
  // end of [remove]
  var removed: int // uninitialized
in
  remove (t, removed) // size = size (t) - removed
end // end of [funmset_remove]

(* ****** ****** *)

(*
** left join: height(tl) >= height(tr)
*)
fun{elt:t@ype}
  avltree_ljoin {hl,hr:nat | hl >= hr} .<hl>.
  (x: elt, n: cnt, tl: avltree (elt, hl), tr: avltree (elt, hr))
  :<> avltree_inc (elt, hl) = let
  val hl = avltree_height (tl) and hr = avltree_height (tr)
in
  if hl - hr >= 2 then let
    val+ B (_, xl, nl, tll, tlr) = tl
    val tlr = avltree_ljoin<elt> (x, n, tlr, tr)
    val hll = avltree_height (tll) and hlr = avltree_height (tlr)
  in
    if hlr - hll <= 1 then begin
      B (max(hll,hlr)+1, xl, nl, tll, tlr)
    end else begin // hll+2 = hlr
      avltree_lrotate (xl, nl, tll, tlr)
    end // end of [if]
  end else begin
    B (hl+1, x, n, tl, tr)
  end // end of [if]
end // end of [avltree_ljoin]

(*
** right join: height(tl) <= height(tr)
*)
fun{elt:t@ype}
  avltree_rjoin {hl,hr:nat | hl <= hr} .<hr>.
  (x: elt, n: cnt, tl: avltree (elt, hl), tr: avltree (elt, hr))
  :<> avltree_inc (elt, hr) = let
  val hl = avltree_height (tl) and hr = avltree_height (tr)
in
  if hr - hl >= 2 then let
    val+ B (_, xr, nr, trl, trr) = tr
    val trl = avltree_rjoin<elt> (x, n, tl, trl)
    val hrl = avltree_height (trl) and hrr = avltree_height (trr)
  in
    if hrl - hrr <= 1 then begin
      B (max(hrl,hrr)+1, xr, nr, trl, trr)
    end else begin // hrl = hrr+2
      avltree_rrotate (xr, nr, trl, trr)
    end // end of [if]
  end else begin
    B (hr+1, x, n, tl, tr)
  end // end of [if]
end // end of [avltree_rjoin]

(* ****** ****** *)

fn{elt:t@ype} avltree_join {hl,hr:nat}
  (x: elt, n: cnt, tl: avltree (elt, hl), tr: avltree (elt, hr))
  :<> [h:int | hl <= h; hr <= h; h <= max(hl,hr)+1] avltree (elt, h) = let
  val hl = avltree_height tl and hr = avltree_height tr
in
  if hl >= hr then
    avltree_ljoin (x, n, tl, tr)
  else
    avltree_rjoin (x, n, tl, tr)
end // end of [avltree_join]

(* ****** ****** *)

fn{elt:t@ype} avltree_concat {hl,hr:nat}
  (tl: avltree (elt, hl), tr: avltree (elt, hr))
  :<> [h:nat | h <= max(hl,hr)+1] avltree (elt, h) = begin
  case+ (tl, tr) of
  | (E (), _) => tr
  | (_, E ()) => tl
  | (_, _) =>> let
      var x_min: elt and n_min: cnt // uninitialized
      val tr = avltree_takeout_min<elt> (tr, x_min, n_min)
    in
      avltree_join (x_min, n_min, tl, tr)
    end // end of [_, _]
end // end of [avltree_concat]

(* ****** ****** *)

typedef avltree = avltree (void, 0)

fun{elt:t@ype}
  avltree_split_at {h:nat} .<h>. (
    t: avltree (elt, h), x0: elt
  , tl0: &avltree? >> avltree (elt, hl)
  , tr0: &avltree? >> avltree (elt, hr)
  , cmp: cmp elt
  ) :<> #[i:nat; hl,hr:nat | hl <= h; hr <= h] int i =
  case t of
  | B (h, x, n, tl, tr) => let
      val sgn = compare_elt_elt<elt> (x0, x, cmp)
    in
      if sgn < 0 then let
        val i = avltree_split_at (tl, x0, tl0, tr0, cmp)
      in
        tr0 := avltree_join (x, n, tr0, tr); i
      end else if sgn > 0 then let
        val i = avltree_split_at (tr, x0, tl0, tr0, cmp)
      in
        tl0 := avltree_join (x, n, tl, tl0); i
      end else begin
        tl0 := tl; tr0 := tr; n // [x] is found in [t]
      end // end of [if]
    end // end of [B]
  | E () => (tl0 := E (); tr0 := E (); 0)
// end of [avltree_split_at]

(* ****** ****** *)

implement{elt} funmset_union (t1, t2, cmp) = uni (t1, t2) where {
  fun uni {h1,h2:nat} .<h1>.
    (t1: avltree (elt, h1), t2: avltree (elt, h2))
    :<cloref> [h:nat] avltree (elt, h) =
    case+ (t1, t2) of
    | (E (), _) => t2 | (_, E ()) => t1 | (_, _) =>> let
        val+ B (_(*h1*), x1, n1, t1l, t1r) = t1
        var t2l0: avltree? and t2r0: avltree?
        val+ i = avltree_split_at (t2, x1, t2l0, t2r0, cmp)
        val t12l = uni (t1l, t2l0) and t12r = uni (t1r, t2r0)
      in
        avltree_join (x1, n1 + i, t12l, t12r)
      end // end of [_, _]
    // end of [uni]
} // end of [funmset_union]

(* ****** ****** *)

implement{elt} funmset_intersect (t1, t2, cmp) = inter (t1, t2) where {
  fun inter {h1,h2:nat} .<h1>.
    (t1: avltree (elt, h1), t2: avltree (elt, h2))
    :<cloref> [h:nat] avltree (elt, h) =
    begin case+ (t1, t2) of
    | (E (), _) => E () | (_, E ()) => E () | (_, _) =>> let
        val+ B (_(*h1*), x1, n1, t1l, t1r) = t1
        var t2l0: avltree? and t2r0: avltree?
        val+ i = avltree_split_at (t2, x1, t2l0, t2r0, cmp)
        val t12l = inter (t1l, t2l0) and t12r = inter (t1r, t2r0)
        val n1 = (if n1 <= i then n1 else i): Nat
      in
        if n1 = 0 then begin
          avltree_concat (t12l, t12r)
        end else begin
          avltree_join (x1, n1, t12l, t12r)
        end // end of [if]
      end // end of [_, _]
    end // end of [inter]
} // end of [funmset_intersect]

(* ****** ****** *)

implement{elt} funmset_diff (t1, t2, cmp) = diff (t1, t2) where {
  fun diff {h1,h2:nat} .<h1>.
    (t1: avltree (elt, h1), t2: avltree (elt, h2)):<cloref>
    [h:nat] avltree (elt, h) = begin case+ (t1, t2) of
    | (E (), _) => E () | (_, E ()) => t1 | (_, _) =>> let
        val+ B (_(*h1*), x1, n1, t1l, t1r) = t1
        var t2l0: avltree? and t2r0: avltree?
        val+ i = avltree_split_at (t2, x1, t2l0, t2r0, cmp)
        val t12l = diff (t1l, t2l0) and t12r = diff (t1r, t2r0)
      in
        if n1 <= i then begin
          avltree_concat (t12l, t12r)
        end else begin
          avltree_join (x1, n1 - i, t12l, t12r)
        end // end of [if]
      end // end of [_, _]
    end // end of [diff]
} // end of [funmset_diff]

(* ****** ****** *)

implement{elt}
  funmset_foreach_clo {v} (pf | t, f) = aux (pf | f, t) where {
  typedef clo_type = (!v | elt, cnt) -<clo> void
  fun aux {h:nat} .<h>.
    (pf: !v | f: &clo_type, t: avltree (elt, h))
    :<> void = begin case+ t of
    | B (_(*h*), x, n, tl, tr) => begin (* inorder traversal *)
        aux (pf | f, tl); f (pf | x, n); aux (pf | f, tr)
      end // end of [B]
    | E () => ()
  end // end of [aux]
} // end of [funmset_foreach_clo]

implement{elt}
  funmset_foreach_cloref (t, f) = let
  val f = __cast (f) where { extern castfn __cast
    (f: (elt, cnt) -<cloref> void):<> (!unit_v | elt, cnt) -<cloref> void
  } // end of [val]
  typedef clo_type = (!unit_v | elt, cnt) -<clo> void
  val (vbox pf_f | p_f) = cloref_get_view_ptr {clo_type} (f)
  prval pf = unit_v ()
  val () = funmset_foreach_clo<elt> {unit_v} (pf | t, !p_f)
  prval unit_v () = pf
in
  // empty
end // end of [funmset_foreach_cloref]

(* ****** ****** *)

(* end of [funmset_avltree.dats] *)
