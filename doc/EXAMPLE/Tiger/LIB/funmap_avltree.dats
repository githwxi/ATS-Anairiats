(*
**
** An implementation of functional maps based on AVL trees.
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

abstype map_t (key: t@ype, itm: t@ype+)

(* ****** ****** *)

typedef cmp (key:t@ype) = (key, key) -<cloref> Sgn

extern fun{key:t@ype}
  compare_key_key (x1: key, x2: key, cmp: cmp key):<> Sgn

implement{key} compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

extern fun{} funmap_empty {key,itm:t@ype} ():<> map_t (key, itm)

//

extern fun{} funmap_is_empty {key,itm:t@ype} (m: map_t (key, itm)):<> bool
extern fun{} funmap_isnot_empty {key,itm:t@ype} (m: map_t (key, itm)):<> bool

//

extern fun{key,itm:t@ype} funmap_size (m: map_t (key, itm)):<> Nat

//

extern fun{key,itm:t@ype}
  funmap_search (m: map_t (key, itm), k0: key, cmp: cmp key):<> Option_vt (itm)

//

extern fun{key,itm:t@ype}
  funmap_insert (m: map_t (key, itm), k0: key, x0: itm, cmp: cmp key):<> map_t (key, itm)

extern fun{key,itm:t@ype} funmap_insert_status
  (m: map_t (key, itm), k0: key, x0: itm, cmp: cmp key, status: &int? >> int)
  :<> map_t (key, itm)

//

extern fun{key,itm:t@ype}
  funmap_remove (m: map_t (key, itm), k0: key, cmp: cmp key):<> map_t (key, itm)

extern fun{key,itm:t@ype} funmap_remove_status
  (m: map_t (key, itm), k0: key, cmp: cmp key, status: &Option_vt itm? >> Option_vt itm)
  :<> map_t (key, itm)

//

extern fun{key,itm:t@ype} funmap_foreach_clo {v:view}
  (pf: !v | xs: map_t (key, itm), f: &(!v | key, itm) -<clo> void):<> void

extern fun{key,itm:t@ype} funmap_foreach_cloref
  (xs: map_t (key, itm), f: (key, itm) -<cloref> void):<!ref> void

//

extern fun{key,itm:t@ype}
  funmap_make_stream_key (xs: map_t (key, itm)): stream_vt key

extern fun{key,itm:t@ype}
  funmap_make_stream_key_itm (xs: map_t (key, itm)): stream_vt @(key, itm)

(* ****** ****** *)

typedef listpos (itm:t@ype) = [n:pos] list (itm, n)

datatype avltree (key:t@ype, itm:t@ype+, int(*height*)) =
  | {hl,hr:nat | hl <= hr+1; hr <= hl+1}
    B (key, itm, max(hl,hr)+1) of
      (int (max(hl,hr)+1), key, listpos itm, avltree (key, itm, hl), avltree (key, itm, hr))
  | E (key, itm, 0)

typedef avltree_inc (key:t@ype, itm:t@ype, h:int) =
  [h1:nat | h <= h1; h1 <= h+1] avltree (key, itm, h1)

typedef avltree_dec (key:t@ype, itm:t@ype, h:int) =
  [h1:nat | h1 <= h; h <= h1+1] avltree (key, itm, h1)

(* ****** ****** *)

assume map_t (key:t@ype, itm:t@ype) = [h:nat] avltree (key, itm, h)

(* ****** ****** *)

implement{} funmap_empty () = E ()

(* ****** ****** *)

implement{} funmap_is_empty (t) =
  case+ t of | B _ => false | E => true
// end of [funmap_is_empty]

implement{} funmap_isnot_empty (t) =
  case+ t of | B _ => true | E => false
// end of [funmap_isnot_empty]

(* ****** ****** *)

implement{key,itm} funmap_size (t) = size (t) where {
  fun size {h:nat} .<h>.
    (t: avltree (key, itm, h)):<> Nat = begin case+ t of
    | B (_(*h*), _(*k*), _(*xs*), tl, tr) => 1 + size (tl) + size (tr)
    | E () => 0
  end // end of [size]
} // end of [funmap_size]

(* ****** ****** *)

implement{key,itm} funmap_search (t, k0, cmp) = search (t) where {
  fun search {h:nat} .<h>.
    (t: avltree (key, itm, h)):<cloref> Option_vt (itm) = begin
    case+ t of
    | B (_(*h*), k, xs, tl, tr) => let
        val sgn = compare_key_key (k0, k, cmp)
      in
        if sgn < 0 then search (tl) else if sgn > 0 then search (tr) else let
          val+ list_cons (x, _) = xs
        in
          Some_vt (x)
        end // end of [if]
      end // end of [B]
    | E () => None_vt ()
  end // end of [search]
} // end of [funmap_search]

(* ****** ****** *)

fn{key,itm:t@ype} avltree_height {h:nat}
  (t: avltree (key, itm, h)):<> int h = begin
  case+ t of | B (h, _, _, _, _) => h | E () => 0
end // end of [avltree_height]

(*
** left rotation for restoring height invariant
*)
fn{key,itm:t@ype} avltree_lrotate {hl,hr:nat | hl+2 == hr} (
    k: key, xs: listpos itm
  , tl: avltree (key, itm, hl)
  , tr: avltree (key, itm, hr)
  ) :<> [h:nat | hr <= h; h <= hr+1] avltree (key, itm, h) = let
  val+ B (hr, kr, xsr, trl, trr) = tr
  val hrl = avltree_height trl and hrr = avltree_height trr
in
  if hrl <= hrr then begin // hr = 1+hlr
    B (hrl+2, kr, xsr, B (hrl+1, k, xs, tl, trl), trr)
  end else let // [hrl > hrr]: deep rotation
    val+ B (_(*hrl*), krl, xsrl, trll, trlr) = trl
  in
    B (hr, krl, xsrl, B (hrl, k, xs, tl, trll), B (hrl, kr, xsr, trlr, trr))
  end // end of [if]
end // end of [avltree_lrotate]

(*
** right rotation for restoring height invariant
*)
fn{key,itm:t@ype} avltree_rrotate {hl,hr:nat | hl == hr+2} (
    k: key, xs: listpos itm
  , tl: avltree (key, itm, hl)
  , tr: avltree (key, itm, hr)
  ) :<> [h:nat | hl <= h; h <= hl+1] avltree (key, itm, h) = let
  val+ B (hl, kl, xsl, tll, tlr) = tl
  val hll = avltree_height tll and hlr = avltree_height tlr
in
  if hll >= hlr then begin // hl = 1+hll
    B (hlr+2, kl, xsl, tll, B (hlr+1, k, xs, tlr, tr))
  end else let // [hll < hlr]: deep rotation
    val+ B (_(*hlr*), klr, xslr, tlrl, tlrr) = tlr
  in
    B (hl, klr, xslr, B (hlr, kl, xsl, tll, tlrl), B (hlr, k, xs, tlrr, tr))
  end // end of [if]
end // end of [avltree_rrotate]

(* ****** ****** *)

macdef list_sing (x) = list_cons (,(x), list_nil ())

implement{key,itm} funmap_insert (t, k0, x0, cmp) = let
  var status: int // uninitialized
in
  funmap_insert_status (t, k0, x0, cmp, status)
end // end of [funmap_insert]

(*
**  [status=1] on return iff [k0] is already in the map
*)
implement{key,itm} funmap_insert_status
  (t, k0, x0, cmp, status) = insert (t, status) where {
  fun insert {h:nat} .<h>.
    (t: avltree (key, itm, h), status: &int? >> int)
    :<cloref> avltree_inc (key, itm, h) = begin case+ t of
    | B (h, k, xs, tl, tr) => let
        val sgn = compare_key_key (k0, k, cmp)
      in
        if sgn < 0 then let
          val tl = insert (tl, status)
          val hl = avltree_height (tl) and hr = avltree_height (tr)
        in
          if hl - hr <= 1 then begin
            B (max(hl, hr) + 1, k, xs, tl, tr)
          end else begin // hl = hr+2
            avltree_rrotate (k, xs, tl, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val tr = insert (tr, status)
          val hl = avltree_height (tl) and hr = avltree_height (tr)
        in
          if hr - hl <= 1 then begin
            B (max(hl, hr) + 1, k, xs, tl, tr)
          end else begin // hl+1 = hr
            avltree_lrotate (k, xs, tl, tr)
          end // end of [if]
        end else begin (* sgn = 0: item already exists *)
          status := 1; B (h, k, list_cons (x0, xs), tl, tr)
        end // end of [if]
      end // end of [B]
    | E () => begin
        status := 0; B (1, k0, list_sing x0, E (), E ())
      end // end of [E]
  end // end of [insert]
} // end of [funmap_insert_status]

(* ****** ****** *)

fun{key,itm:t@ype} avltree_takeout_min {h:pos} .<h>. (
    t: avltree (key, itm, h)
  , k0: &key? >> key
  , xs0: &listpos itm? >> listpos itm
  ) :<> avltree_dec (key, itm, h) = let
  val+ B (_, k, xs, tl, tr) = t
in
  case+ tl of
  | B _ => let
      val tl = avltree_takeout_min<key,itm> (tl, k0, xs0)
      val hl = avltree_height (tl) and hr = avltree_height (tr)
    in
      if hr - hl <= 1 then begin
        B (max(hl,hr)+1, k, xs, tl, tr)
      end else begin // hl+2 = hr
       avltree_lrotate (k, xs, tl, tr)
      end // end of [if]
    end // end of [B]
  | E () => (k0 := k; xs0 := xs; tr)
end // end of [avltree_takeout_min]

(* ****** ****** *)

dataview ptrat0 (itm:t@ype+, addr) =
  | {l:addr | l <> null} ptrat0_some (itm, l) of itm @ l
  | ptrat0_none (itm, null)

dataview ptrat1 (itm:viewt@ype+, addr) =
  | {l:addr | l <> null} ptrat1_some (itm, l) of itm @ l
  | ptrat1_none (itm, null)

viewdef ptratopt0 (itm:t@ype, l:addr) = ptrat0 (Option_vt itm?, l)
viewdef ptratopt1 (itm:t@ype, l:addr) = ptrat1 (Option_vt itm , l)

fn{key,itm:t@ype}
  funmap_remove_main {l:addr} (
    pf: !ptratopt0 (itm, l) >> ptratopt1 (itm, l)
  | m: map_t (key, itm), k0: key, cmp: cmp key, p: ptr l
  ) :<> map_t (key, itm) = remove (pf | m) where {
  fun remove {h:nat} .<h>. (
      pf: !ptratopt0 (itm, l) >> ptratopt1 (itm, l)
    | t: avltree (key, itm, h)
    ) :<cloref> avltree_dec (key, itm, h) = begin case+ t of
    | B (h, k, xs, tl, tr) => let
        val sgn = compare_key_key (k0, k, cmp)
      in
        if sgn < 0 then let
          val tl = remove (pf | tl)
          val hl = avltree_height tl and hr = avltree_height tr
        in
          if hr - hl <= 1 then begin
            B (max(hl,hr) + 1, k, xs, tl, tr)
          end else begin // hl+2 == hr
            avltree_lrotate (k, xs, tl, tr)
          end // end of [if]
        end else if sgn > 0 then let
          val tr = remove (pf | tr)
          val hl = avltree_height tl and hr = avltree_height tr
        in
          if hl - hr <= 1 then begin
            B (max(hl,hr) + 1, k, xs, tl, tr)
          end else begin // hl = hr+2
            avltree_rrotate (k, xs, tl, tr)
          end // end of [if]
        end else let (* sgn = 0: item found *)
          val+ list_cons (x, xs) = xs
          val () =
            if :(pf: ptratopt1 (itm, l)) => p <> null then let
              prval ptrat0_some pf1 = pf
            in
              !p := Some_vt x; pf := ptrat1_some (pf1)
            end else let
              prval ptrat0_none () = pf in pf := ptrat1_none ()
            end // end of [if]
        in
          case+ xs of
          | list_cons _ => B (h, k, xs, tl, tr)
          | list_nil () => begin case+ tr of
            | B _ => let
                var k_min: key? and xs_min: listpos itm?
                val tr = avltree_takeout_min<key,itm> (tr, k_min, xs_min)
                val hl = avltree_height tl and hr = avltree_height tr
              in
                if hl - hr <= 1 then begin
                  B (max(hl,hr)+1, k_min, xs_min, tl, tr)
                end else begin // hl+2 = hr
                  avltree_rrotate (k_min, xs_min, tl, tr)
                end // end of [if]
              end // end of [B]
            | E () => tl
            end // end of [list_nil]
        end // end of [if]
      end // end of [B]
    | E () => let
        val () =
          if :(pf: ptratopt1 (itm, l)) => p <> null then let
            prval ptrat0_some pf1 = pf
          in
            !p := None_vt (); pf := ptrat1_some (pf1)
          end else let
            prval ptrat0_none () = pf in pf := ptrat1_none ()
          end // end of [if]
      in
        E () // no association for the key [k0]
      end // end of [E]
  end // end of [remove]
} // end of [funmap_remove_main]

(* ****** ****** *)

implement{key,itm} funmap_remove (m, k0, cmp) = let
  prval pf = ptrat0_none {Option_vt itm?} ()
  val m = funmap_remove_main<key,itm> (pf | m, k0, cmp, null)
  prval ptrat1_none () = pf
in
  m // map after removal operation is performed
end // end of [funmap_remove]

(*
**  [status=Some_vt(x)] on return iff [k0->x] is in the map
*)
implement{key,itm} funmap_remove_status (m, k0, cmp, status) = let
  prval pf = ptrat0_some {Option_vt itm?} (view@ status)
  val m = funmap_remove_main<key,itm> (pf | m, k0, cmp, &status)
  prval ptrat1_some (pf1) = pf; prval () = view@ status := pf1
in
  m // map after removal operation is performed
end // end of [funmap_remove_status]

(* ****** ****** *)

implement{key,itm}
  funmap_foreach_clo {v} (pf | t, f) = aux (pf | f, t) where {
  viewtypedef clo_type = (!v | key, itm) -<clo> void
  fun aux {h:nat} .<h>. (
      pf: !v | f: &clo_type, t: avltree (key, itm, h)
    ) :<> void = begin case+ t of
    | B (_(*h*), k, xs, tl, tr) => let (* inorder traversal *)
        val+ list_cons (x, _) = xs
      in
        aux (pf | f, tl); f (pf | k, x); aux (pf | f, tr)
      end // end of [B]
    | E () => ()
  end // end of [aux]
} // end of [funmap_foreach_clo]

implement{key,itm}
  funmap_foreach_cloref (t, f) = let
  val f = __cast (f) where { extern castfn __cast
    (f: (key, itm) -<cloref> void):<> (!unit_v | key, itm) -<cloref> void
  } // end of [val]
  typedef clo_type = (!unit_v | key, itm) -<clo> void
  val (vbox pf_f | p_f) = cloref_get_view_ptr {clo_type} (f)
  prval pf = unit_v ()
  val () = $effmask_ref (funmap_foreach_clo<key,itm> {unit_v} (pf | t, !p_f))
  prval unit_v () = pf
in
  // empty
end // end of [funmap_foreach_cloref]

(* ****** ****** *)

implement{key,itm}
  funmap_make_stream_key (t) = _make1 (t) where {
  fun _make1 {h:nat}
    (t: avltree (key, itm, h))
    :<1,~ref> stream_vt key = $ldelay (begin case+ t of
    | B (_(*h*), k, _(*xs*), tl, tr) => let
        val ks1 = _make1 (tl)
        val ks1_con = !ks1 in case+ ks1_con of
          | stream_vt_cons (k1, !p_ks1) => let
              val () = !p_ks1 := _make2 (!p_ks1, k, tr) in
              fold@ ks1_con; ks1_con
            end // end of [stream_vt_cons]
          | ~stream_vt_nil () => stream_vt_cons (k, _make1 tr)
      end // end of [B]
    | E () => stream_vt_nil ()
  end : stream_vt_con key) // end of [_make1]

  and _make2 {h:nat} (
      ks1: stream_vt key
    , k: key
    , tr: avltree (key, itm, h)
    ) :<1,~ref> stream_vt key = $ldelay (
    let val ks1_con = !ks1 in case+ ks1_con of
      | stream_vt_cons (k1, !p_ks1) => let
          val () = !p_ks1 := _make2 (!p_ks1, k, tr) in
          fold@ ks1_con; ks1_con
        end // end of [stream_vt_cons]
      | ~stream_vt_nil () => stream_vt_cons (k, _make1 tr)
    end : stream_vt_con key
  , stream_vt_free (ks1)
  ) // end of [_make2]
} // end of [funmap_make_stream_key]

(* ****** ****** *)

implement{key,itm}
  funmap_make_stream_key_itm (t) = _make1 (t) where {
  typedef keyitm = @(key, itm)
  fun _make1 {h:nat}
    (t: avltree (key, itm, h))
    :<1,~ref> stream_vt keyitm = $ldelay (begin case+ t of
    | B (_(*h*), k, xs, tl, tr) => let
        val kis1 = _make1 (tl)
        val+ list_cons (x, _) = xs
        val kis1_con = !kis1 in case+ kis1_con of
          | stream_vt_cons (k1, !p_kis1) => let
              val () = !p_kis1 := _make2 (!p_kis1, k, x, tr) in
              fold@ kis1_con; kis1_con
            end // end of [stream_vt_cons]
          | ~stream_vt_nil () => stream_vt_cons (@(k, x), _make1 tr)
      end // end of [B]
    | E () => stream_vt_nil ()
  end : stream_vt_con keyitm) // end of [_make1]

  and _make2 {h:nat} (
      kis1: stream_vt keyitm
    , k: key, x: itm
    , tr: avltree (key, itm, h)
    ) :<1,~ref> stream_vt keyitm = $ldelay (
    let val kis1_con = !kis1 in case+ kis1_con of
      | stream_vt_cons (k1, !p_kis1) => let
          val () = !p_kis1 := _make2 (!p_kis1, k, x, tr) in
          fold@ kis1_con; kis1_con
        end // end of [stream_vt_cons]
      | ~stream_vt_nil () => stream_vt_cons (@(k, x), _make1 tr)
    end : stream_vt_con keyitm
  , stream_vt_free (kis1)
  ) // end of [_make2]
} // end of [funmap_make_stream_key]

(* ****** ****** *)

(* end of [funmap_avltree.dats] *)
