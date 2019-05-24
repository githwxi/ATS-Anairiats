(*
**
** An implementation of linear queues based on lists
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: October, 2008
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

staload "prelude/SATS/slseg.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

absviewtype linqueuelst_vt
  (a:viewt@ype (*element*), n:int (*size*))

stadef queue = linqueuelst_vt // an abbreviation

(* ****** ****** *)

// always inline
extern fun{} linqueuelst_nil {a:viewt@ype} ():<> queue (a, 0)

(* ****** ****** *)

// always inline
extern fun{} linqueuelst_is_nil {a:viewt@ype}
  {n:nat} (xs: !queue (a, n)):<> bool (n==0)

// always inline
extern fun{} linqueuelst_is_cons {a:viewt@ype}
  {n:nat} (xs: !queue (a, n)):<> bool (n > 0)

(* ****** ****** *)

extern fun{a:viewt@ype} linqueuelst_enqueue {n:nat} // O(1)
  (xs: &queue (a, n) >> queue (a, n+1), x: a):<> void

extern fun{a:viewt@ype} linqueuelst_dequeue {n:pos} // O(1)
  (xs: &queue (a, n) >> queue (a, n-1)):<> a

(* ****** ****** *)

// only allowed for a queue storing nonlinear elements.
extern fun{a:t@ype} linqueuelst_fst {n:pos} (xs: &queue (a, n)):<> a

(* ****** ****** *)

extern fun{a:viewt@ype} linqueuelst_size {n:nat} (xs: !queue (a, n)):<> int n

(* ****** ****** *)

extern fun{a:viewt@ype} list_vt_of_linqueuelst {n:nat} (xs: queue (a, n)): list_vt (a, n)

(* ****** ****** *)

extern fun{a:viewt@ype}
  linqueuelst_foreach_cloptr {v:view} {n:nat} {f:eff}
  (pf: !v | xs: !queue (a, n), f: !(!v | &a) -<cloptr,f> void):<f> void

extern fun{a:viewt@ype}
  linqueuelst_foreach_cloref {v:view} {n:nat} {f:eff}
  (pf: !v | xs: !queue (a, n), f: !(!v | &a) -<cloref,f> void):<f> void

(* ****** ****** *)

dataviewtype queuelst_vt (a:viewt@ype+, int) =
  | {n:nat} {l1,l2,l3:addr}
    queuelst_vt_some (a, n+1) of (
      slseg_v (a, l1, l2, n), free_gc_v l2, (a, ptr?) @ l2 | int n, ptr l1, ptr l2
    ) // end of [queuelst_vt_some]
  | queuelst_vt_none (a, 0) of ()

assume linqueuelst_vt (a: viewt@ype, n: int) = queuelst_vt (a, n)

(* ****** ****** *)

implement{} linqueuelst_nil () = queuelst_vt_none ()

implement{} linqueuelst_is_nil (xs) = begin case+ xs of
  | queuelst_vt_some (_, _, _| _, _, _) => (fold@ xs; false)
  | queuelst_vt_none () => (fold@ xs; true)
end // end of [linqueuelst_is_nil]

implement{} linqueuelst_is_cons (xs) = begin case+ xs of
  | queuelst_vt_some (_, _, _ | _, _, _) => (fold@ xs; true)
  | queuelst_vt_none () => (fold@ xs; false)
end // end of [linqueuelst_is_cons]

(* ****** ****** *)

implement{a} linqueuelst_size (xs) = begin case+ xs of
  | queuelst_vt_some
      (!pf_seg, _(*pf_gc*), _(*pf_at*) | n, _(*p1*), _(*p2*)) => (fold@ xs; n + 1)
  | queuelst_vt_none () => (fold@ xs; 0)
end // end of [linqueuelst_size]

(* ****** ****** *)

implement{a} linqueuelst_enqueue (xs, x) = let
  viewtypedef VT = @(a, ptr?)
  val (pf_gc_new, pf_at_new | p_new) = ptr_alloc<VT> ()
  val () = p_new->0 := x
in
  case+ xs of
  | queuelst_vt_some
      (!pf_seg_r, !pf_gc_r, !pf_at_r | !n_r, p1, !p2_r) => let
      stavar l2: addr
      prval pf_seg = !pf_seg_r
      prval pf_gc = !pf_gc_r and pf_at = !pf_at_r: VT @ l2
      val p2 = !p2_r; val () = p2->1 := p_new
      prval pf_seg_new = slseg_v_extend (pf_seg, pf_gc, pf_at)
      prval () = begin
        !pf_seg_r := pf_seg_new; !pf_gc_r := pf_gc_new; !pf_at_r := pf_at_new
      end // end of [prval]
    in
      !n_r := !n_r + 1; !p2_r := p_new; fold@ xs
    end // end of [queuelst_vt_some]
  | queuelst_vt_none () => begin
      xs := queuelst_vt_some (slseg_v_nil (), pf_gc_new, pf_at_new | 0, p_new, p_new)
    end // end of [queuelst_vt_none]
end // end of [linqueuelst_enqueue]

implement{a} linqueuelst_dequeue (xs) = let
  typedef T = @(a?, ptr?)
  val+ queuelst_vt_some (!pf_seg_r, !pf_gc_r, !pf_at_r | !n_r, !p1_r, p2) = xs
  prval pf_seg = !pf_seg_r
  val n = !n_r and p1 = !p1_r
in
  if n > 0 then let
    prval slseg_v_cons (pf_gc, pf_at, pf_seg) = pf_seg
    val x = p1->0; val () = !p1_r := p1->1
    val () = ptr_free {T} (pf_gc, pf_at | p1)
  in
    !pf_seg_r := pf_seg; !n_r := n - 1; fold@ xs; x
  end else let
    prval slseg_v_nil () = pf_seg
    prval pf_gc = !pf_gc_r and pf_at = !pf_at_r
    val x = p2->0; val () = ptr_free {T} (pf_gc, pf_at | p2)
  in
    free@ {..} {0} (xs); xs := queuelst_vt_none (); x
  end // end of [if]
end // end of [linqueuelst_deqeue]

(* ****** ****** *)

implement{a:t@ype} linqueuelst_fst (xs) = let
  val+ queuelst_vt_some (!pf_seg_r, _, !pf_at_r | n, p1, p2) = xs
in
  if n > 0 then let
    prval slseg_v_cons (pf1_gc, pf1_at, pf1_seg) = !pf_seg_r; val x = p1->0
  in
    !pf_seg_r := slseg_v_cons (pf1_gc, pf1_at, pf1_seg); fold@ xs; x
  end else let
    prval pf_at = !pf_at_r; val x = p2->0 in !pf_at_r := pf_at; fold@ xs; x
  end // end of [if]
end // end of [linqueuelst_fst]

(* ****** ****** *)

implement{a} list_vt_of_linqueuelst (xs) = case+ xs of
  | ~queuelst_vt_some (pf_seg, pf_gc, pf_at | _, p1, p2) => let
      viewtypedef VT = (a, ptr?)
      stavar l2: addr; prval pf_at = pf_at: VT @ l2
    in
      p2->1 := null; list_vt_of_sllst (slseg_v_extend (pf_seg, pf_gc, pf_at) | p1)
    end
  | ~queuelst_vt_none () => list_vt_nil ()
// end of [list_vt_of_linqueuelst]

(* ****** ****** *)

implement{a} linqueuelst_foreach_cloptr (pf | xs, f) = begin
  case+ xs of
  | queuelst_vt_some (!pf_seg_r, !pf_gc_r, !pf_at_r | n, p1, p2) => let
      prval pf_at = !pf_at_r
      val () = slseg_foreach_cloptr<a> (pf, !pf_seg_r | p1, n, f)
      val () = f (pf | p2->0)
    in
      !pf_at_r := pf_at; fold@ (xs)
    end
  | queuelst_vt_none () => fold@ (xs)
end // end of [linqueuelst_foreach_cloptr]

implement{a}
  linqueuelst_foreach_cloref {v} {n} {f} (pf0 | xs, f) = let
  typedef cloref_type = (!v | &a) -<cloref, f> void
  viewtypedef cloptr_type = (!v | &a) -<cloptr, f> void
  val f = cloref_cloptr_make (f) where {
    extern fun cloref_cloptr_make (f: cloref_type):<> cloptr_type
      = "atspre_cloref_cloptr_make"
  } // end of [where]
  val () = linqueuelst_foreach_cloptr<a> {v} (pf0 | xs, f)
  val () = cloref_cloptr_free (f) where {
    extern fun cloref_cloptr_free (f: cloptr_type):<> void
      = "atspre_cloref_cloptr_free"
  } // end of [where]
in
  // empty
end // end of [linqueuelst_foreach_cloref]

(* ****** ****** *)

(* end of [linqueuelst.dats] *)
