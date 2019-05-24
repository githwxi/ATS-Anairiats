(*
**
** An implementation of functional maps based on AVL trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

// An implementation of linear maps based on randomized binary search trees

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

absviewtype map_vt (key: t@ype, itm: viewt@ype+)

(* ****** ****** *)

typedef cmp (key:t@ype) = (key, key) -<cloref> Sgn

extern fun{key:t@ype}
  compare_key_key (x1: key, x2: key, cmp: cmp key):<> Sgn

implement{key} compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(*
implement compare_key_key<int=int> (x1, x2, _) = compare (x1, x2)
implement compare_key_key<string=string> (x1, x2, _) = compare (x1, x2)
*)

(* ****** ****** *)

extern fun{} linmap_empty {key:t@ype;itm:viewt@ype} ():<> map_vt (key, itm)

//

extern fun{} linmap_is_empty
  {key:t@ype;itm:viewt@ype} (m: !map_vt (key, itm)):<> bool
extern fun{} linmap_isnot_empty
  {key:t@ype;itm:viewt@ype} (m: !map_vt (key, itm)):<> bool

//

extern fun{key:t@ype;itm:viewt@ype} linmap_size (m: !map_vt (key, itm)):<> Nat

// mostly used for gathering statistics
extern fun{key:t@ype;itm:viewt@ype} linmap_height (m: !map_vt (key, itm)):<> Nat

//

extern fun{key:t@ype;itm:t@ype} linmap_free (m: map_vt (key, itm)):<> void

//

extern fun{key:t@ype;itm:t@ype}
  linmap_search (m: !map_vt (key, itm), k0: key, cmp: cmp key):<> Option_vt (itm)

//

// this one is reentrant
extern fun{key:t@ype;itm:viewt@ype} linmap_insert
  (m: &map_vt (key, itm), k0: key, x0: itm, cmp: cmp key):<> Option_vt itm

//

// this one is reentrant
extern fun{key:t@ype;itm:viewt@ype} linmap_remove
  (m: &map_vt (key, itm), k0: key, cmp: cmp key):<> Option_vt itm

//

extern fun{key:t@ype;itm:viewt@ype} linmap_foreach_clo {v:view}
  (pf: !v | xs: !map_vt (key, itm), f: &(!v | key, &itm) -<clo> void):<> void

extern fun{key:t@ype;itm:viewt@ype} linmap_foreach_cloref
  (xs: !map_vt (key, itm), f: (key, &itm) -<cloref> void):<!ref> void

(* ****** ****** *)

// a dataviewtype for binary search trees
dataviewtype bst (key:t@ype, itm:viewt@ype+, int(*height*)) =
  | {nl,nr:nat} BSTcons (key, itm, 1+nl+nr) of
      (int (1+nl+nr), key, itm, bst (key, itm, nl), bst (key, itm, nr))
  | BSTnil (key, itm, 0)
// end of [bst]

(* ****** ****** *)

fn{key:t@ype;itm:viewt@ype}
  bst_size {n:nat} (t: !bst (key, itm, n)):<> int n = case+ t of
  | BSTcons (n, _, _, _, _) => (fold@ t; n) | BSTnil _ => (fold@ t; 0) 
// end of [bst_size]

fun{key:t@ype;itm:viewt@ype}
  bst_height {n:nat} .<n>. (t: !bst (key, itm, n)):<> Nat =
  case+ t of
  | BSTcons (_, _, _, !p_tl, !p_tr) => let
      val nl = bst_height !p_tl
      and nr = bst_height !p_tr in (fold@ t; 1 + max (nl, nr))
    end // end of [BSTcons]
  | BSTnil _ => (fold@ t; 0) 
// end of [bst_height]

(* ****** ****** *)

fn{key:t@ype;itm:viewt@ype}
  bst_is_nil {n:nat}(t: !bst (key, itm, n)):<> bool (n == 0) =
  case+ t of BSTcons _ => (fold@ t; false) | BSTnil _ => (fold@ t; true)
// end of [bst_is_nil]

fn{key:t@ype;itm:viewt@ype}
  bst_is_cons {n:nat}(t: !bst (key, itm, n)):<> bool (n > 0) =
  case+ t of BSTcons _ => (fold@ t; true) | BSTnil _ => (fold@ t; false)
// end of [bst_is_cons]

(* ****** ****** *)

fun{key:t@ype;itm:t@ype}
  bst_free {n:nat} .<n>. (t: bst (key, itm, n)):<> void =
  case+ t of
  | ~BSTcons (_, _, _, tl, tr) => (bst_free tl; bst_free tr)
  | ~BSTnil () => ()
// end of [bst_free]

(* ****** ****** *)

fun{key:t@ype;itm:t@ype}
  bst_search {n:nat} .<n>. (
    t: !bst (key, itm, n)
  , k0: key, cmp: cmp key
  ) :<> Option_vt itm = begin case+ t of
  | BSTcons (_, k, !p_i, !p_tl, !p_tr) => let
      val sgn = compare_key_key (k0, k, cmp) in case+ sgn of
        | ~1 => let
            val ans = bst_search (!p_tl, k0, cmp) in fold@ t; ans
          end // end of [~1]
        |  1 => let
            val ans = bst_search (!p_tr, k0, cmp) in fold@ t; ans
          end // end of [ 1]
        |  _ (*0*) => begin
            let val ans = Some_vt (!p_i) in fold@ t; ans end
          end // end of [_]
    end // end of [BSTcons]
  | BSTnil () => begin
      fold@ t; None_vt ()
    end // end of [BSTnil]
end (* end of [bst_search] *)

(* ****** ****** *)

// preorder foreach
fun{key:t@ype;itm:viewt@ype}
  bst_foreach_pre {v:view} {vt:viewtype} {n:nat} {f:eff} .<n>. (
    pf: !v
  | t: !bst (key, itm, n)
  , f: (!v | key, &itm, !vt) -<f> void
  , env: !vt
  ) :<f> void = begin case+ t of
  | BSTcons (_, k, !p_i, !tl, !tr) => let
      val () = bst_foreach_pre (pf | !tl, f, env)
      val () = f (pf | k, !p_i, env)
      val () = bst_foreach_pre (pf | !tr, f, env)
    in
      fold@ t
    end // end of [BSTcons]
  | BSTnil () => fold@ t
end // end of [bst_foreach_pre]

(* ****** ****** *)

staload "libc/SATS/random.sats"

extern fun dice
  {m,n:int | m > 0; n > 0}
  (m: int m, n: int n, buf: &drand48_data):<> bool
// end of [dice]

implement dice (m, n, buf) = let
  var r: int // uninitialized
  val () = randint_r (buf, m+n, r) in if r < m then true else false
end // end of [dice]

(* ****** ****** *)

fun{key:t@ype;itm:viewt@ype}
  bst_insert_atroot {n:nat} .<n>. (
    t: &bst (key, itm, n) >> bst (key, itm, n+1-i)
  , k0: key, i0: itm, cmp: cmp key, r: &int? >> int i
  ) :<> #[i:two] option_vt (itm, i > 0) = begin
  case+ t of
  | BSTcons
      (!p_n, k, _(*i*), !p_tl, !p_tr) => let
      val sgn = compare_key_key (k0, k, cmp) in
      if sgn < 0 then let
        val ans = bst_insert_atroot<key,itm> (!p_tl, k0, i0, cmp, r)
      in
        if r = 0 then let
          val tl_new = !p_tl
          val+ BSTcons (!p_nl, _(*kl*), _(*il*), !p_tll, !p_tlr) = tl_new
          val n = !p_n; val nll = bst_size !p_tll
        in
          !p_tl := !p_tlr; !p_n := n - nll; fold@ t;
          !p_tlr := t; !p_nl := n + 1; fold@ tl_new;
          t := tl_new; ans
        end else begin
          fold@ t; ans // [k0] is alreay in the binary search tree
        end // end of [if]
      end else if sgn > 0 then let
        val ans = bst_insert_atroot<key,itm> (!p_tr, k0, i0, cmp, r)
      in
        if r = 0 then let
          val tr_new = !p_tr
          val+ BSTcons (!p_nr, _(*kr*), _(*ir*), !p_trl, !p_trr) = tr_new
          val n = !p_n; val nrr = bst_size !p_trr
        in
          !p_tr := !p_trl; !p_n := n - nrr; fold@ t;
          !p_trl := t; !p_nr := n + 1; fold@ tr_new;
          t := tr_new; ans
        end else begin
          fold@ t; ans // [k0] is alreay in the binary search tree
        end // end of [if]
      end else begin (* sgn = 0 *)
        fold@ t; r := 1; Some_vt (i0)
      end // end of [if]
    end (* end of [BSTcons] *)
  | ~BSTnil () => begin
      t := BSTcons (1, k0, i0, BSTnil (), BSTnil ()); r := 0; None_vt ()
    end // end of [BSTnil]
end (* end of [bst_insert_atroot] *)

fun{key:t@ype;itm:viewt@ype}
  bst_insert_random {n:nat} .<n>. (
    t: &bst (key, itm, n) >> bst (key, itm, n+1-i)
  , k0: key, i0: itm, cmp: cmp key, r: &int? >> int i
  , buf: &drand48_data
  ) :<> #[i:two] option_vt (itm, i > 0) = begin case+ t of
  | BSTcons (!p_n, k, _(*i*), !p_tl, !p_tr) =>
    if dice (1, !p_n, buf) then begin
      fold@ t; bst_insert_atroot<key,itm> (t, k0, i0, cmp, r)
    end else let
      val sgn = compare_key_key (k0, k, cmp) in
      if sgn < 0 then let
        val ans = bst_insert_random<key,itm> (!p_tl, k0, i0, cmp, r, buf) in
        if r = 0 then (!p_n := !p_n + 1; fold@ t; ans) else (fold@ t; ans)
      end else if sgn > 0 then let
        val ans = bst_insert_random<key,itm> (!p_tr, k0, i0, cmp, r, buf) in
        if r = 0 then (!p_n := !p_n + 1; fold@ t; ans) else (fold@ t; ans)
      end else begin (* sgn = 0 *)
        fold@ t; r := 1; Some_vt (i0)
      end // end of [if]
    end (* end of [BSTcons] *)
  | ~BSTnil () => begin
      t := BSTcons (1, k0, i0, BSTnil (), BSTnil ()); r := 0; None_vt ()
    end (* end of [BSTnil] *)
end (* end of [bst_insert_random] *)

(* ****** ****** *)

fun{key:t@ype;itm:viewt@ype}
  bst_join_random {nl,nr:nat} .<nl+nr>. (
    tl: bst (key, itm, nl)
  , tr: bst (key, itm, nr)
  , buf: &drand48_data
  ) :<> bst (key, itm, nl+nr) = begin case+ tl of
  | BSTcons
      (!p_nl, _(*kl*), _(*il*), !p_tll, !p_tlr) => begin
    case+ tr of
    | BSTcons (!p_nr, _(*kr*), _(*ir*), !p_trl, !p_trr) => let
        val n = !p_nl + !p_nr
      in
        if dice (!p_nl, !p_nr, buf) then begin
          fold@ tr; !p_tlr := bst_join_random (!p_tlr, tr, buf);
          !p_nl := n; fold@ tl; tl
        end else begin
          fold@ tl; !p_trl := bst_join_random (tl, !p_trl, buf);
          !p_nr := n; fold@ tr; tr
        end // end of [if]
      end (* end of [BSTcons] *)
    | ~BSTnil () => (fold@ tl; tl)
    end (* end of [BSTcons] *)
  | ~BSTnil () => tr
end // end of [bst_join_random]

(* ****** ****** *)

fun{key:t@ype;itm:viewt@ype}
  bst_remove_random {n:nat} {l1,l2:addr} .<n>. (
    t: &bst (key, itm, n) >> bst (key, itm, n-i)
  , k0: key, cmp: cmp key
  , r: &int? >> int i
  , buf: &drand48_data
  ) :<> #[i:two | i <= n] option_vt (itm, i > 0) = begin
  case+ t of
  | BSTcons {..} {nl,nr}
      (!p_n, k, !p_i, !p_tl, !p_tr) => let
      val sgn = compare_key_key (k0, k, cmp) in case+ sgn of
      | ~1 => let
          val ans = bst_remove_random (!p_tl, k0, cmp, r, buf) in
          !p_n := !p_n - r; fold@ t; ans
        end // end of [~1]
      |  1 => let
          val ans = bst_remove_random (!p_tr, k0, cmp, r, buf) in
          !p_n := !p_n - r; fold@ t; ans
        end // end of [1]
      |  _ (* 0 *) => let
          val ans = Some_vt (!p_i)
          val t_new = bst_join_random (!p_tl, !p_tr, buf) in
          r := 1; free@ {key,itm} {0,0} (t); t := t_new; ans
        end // end of [0]
    end (* end of [BSTcons] *)
  | BSTnil () => (r := 0; fold@ t; None_vt ())
end // end of [bst_remove_random]

(* ****** ****** *)

assume map_vt (key:t@ype, itm:viewt@ype) = [s:nat] bst (key, itm, s)

(* ****** ****** *)

implement{} linmap_empty () = BSTnil ()

(* ****** ****** *)

implement{} linmap_is_empty (m) = case+ m of
  | BSTcons _ => (fold@ m; false) | BSTnil () => (fold@ m; true)
// end of [linmap_is_empty]

implement{} linmap_isnot_empty (m) = case+ m of
  | BSTcons _ => (fold@ m; true) | BSTnil () => (fold@ m; false)
// end of [linmap_isnot_empty]

(* ****** ****** *)

implement{key,itm} linmap_size (m) = case+ m of
  | BSTcons (n, _, _, _, _) => (fold@ m; n) | BSTnil () => (fold@ m; 0)
// end of [linmap_size]

implement{key,itm} linmap_height (m) = bst_height (m)

(* ****** ****** *)

implement{key,itm} linmap_free (m) = bst_free<key,itm> (m)

(* ****** ****** *)

implement{key,itm}
  linmap_search (m, k0, cmp) = bst_search<key,itm> (m, k0, cmp)
// end of [linmap_search]

(* ****** ****** *)

implement{key,itm}
  linmap_insert (m, k0, i0, cmp) = let
  var r: int (* uninitialized *)
  var buf: drand48_data // uinitialized
  val _(*0*) = srand48_r (0L, buf) in
  bst_insert_random<key,itm> (m, k0, i0, cmp, r, buf)
end // end of [linmap_insert]

(* ****** ****** *)

implement{key,itm}
  linmap_remove (m, k0, cmp) = let
  var r: int (* uninitialized *)
  var buf: drand48_data // uinitialized
  val _(*0*) = srand48_r (0L, buf) in
  bst_remove_random<key,itm> (m, k0, cmp, r, buf)
end // end of [linmap_remove]

(* ****** ****** *)

implement{key,itm}
  linmap_foreach_clo {v} (pf1 | m, f) = let
  viewtypedef clo_t = (!v | key, &itm) -<clo> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | k: key, i: &itm, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | k, i)
    prval () = pf := (pf1, pf2)
  in
    // empty
  end // end of [app]
  prval pf2 = view@ f; prval pf = (pf1, pf2)
  val () = bst_foreach_pre<key,itm> {V} {ptr l_f} (pf | m, app, p_f)
  prval () = (pf1 := pf.0; view@ f := pf.1)
in
  // empty
end // end of [linmap_foreach_clo]

implement{key,itm}
  linmap_foreach_cloref (m, f) = let
  typedef cloref_t = (key, &itm) -<cloref> void
  fn app (pf: !unit_v | k: key, i: &itm, f: !cloref_t):<> void = f (k, i)
  prval pf = unit_v ()
  val () = bst_foreach_pre<key,itm> {unit_v} {cloref_t} (pf | m, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [linmap_foreach_cloref]

(* ****** ****** *)

(* end of [linmap_randbst.dats] *)
