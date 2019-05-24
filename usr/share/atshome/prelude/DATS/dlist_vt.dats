(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2012 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // HX: no need for dynloading at run-time

(* ****** ****** *)

staload
UN = "prelude/SATS/unsafe.sats"
staload "prelude/SATS/dlist_vt.sats"

(* ****** ****** *)

sortdef t0p = t@ype
sortdef vt0p = viewt@ype

(* ****** ****** *)

dataviewtype
DLIST (a:viewt@ype+, int) =
  | {r:nat}
    DLISTcons (a, r+1) of (a, ptr(*prev*), DLIST (a, r))
  | DLISTnil (a, 0) of ()
// end of [DLIST]

extern
castfn dlist2ptr {a:vt0p}{r:int} (xs: !DLIST(a, r)):<> ptr

(* ****** ****** *)

assume
dlist_viewt0ype_int_int_viewtype
  (a: vt0p, f:int, r:int) = DLIST (a, r)
// end of [assume]

(* ****** ****** *)

implement{a} dlist_vt_nil () = DLISTnil ()

(* ****** ****** *)

implement{a}
dlist_vt_cons (x, xs) =
  case+ xs of
  | DLISTcons
      (_, !p_prev, _) => let
      prval () = fold@ (xs)
      val res = DLISTcons (x, null, xs)
      prval () = __assert (p_prev) where {
        extern praxi __assert {l:addr} (p: ptr l): [l > null] void
      } // end of [prval]
      val () = $UN.ptrset<ptr> (p_prev, dlist2ptr(res))
    in
      res
    end // end of [DLISTcons]
  | ~DLISTnil () => DLISTcons (x, null, DLISTnil ())
// end of [dlist_vt_cons]

(* ****** ****** *)

implement{a}
dlist_vt_snoc (xs, x) = let
  val node =
    DLISTcons (x, dlist2ptr(xs), DLISTnil ())
  val node1 = __copy (node) where {
    extern castfn __copy (xs: !DLIST(a, 1)):<> DLIST(a, 1)
  }
  val+ DLISTcons (_, prev, !p_xs) = xs
  val+ DLISTnil () = !p_xs; val () = !p_xs := node1
  prval () = fold@ {a} (xs)
  prval () = __hide (xs) where {
    extern praxi __hide (xs: DLIST(a, 2)):<> void
  } // end of [prval]
in
  node
end // end of [dlist_vt_snoc]

(* ****** ****** *)

implement{a}
dlist_vt_get
  {f,r} (xs) = let
  val+ DLISTcons (x, _, _) = xs in fold@ (xs); x
end // end of [dlist_vt_get]

implement{a}
dlist_vt_set
  {f,r} (xs, x) = let
  val+ DLISTcons (!p_x, _, _) = xs in !p_x := x; fold@ (xs)
end // end of [dlist_vt_set]

(* ****** ****** *)

implement{a}
dlist_vt_is_beg
  {f,r} (xs) = let
  val+ DLISTcons (_, prev, _) = xs
  prval () = fold@ (xs)
  val [b:bool] ans = (
    if prev > null then false else true
  ) : Bool // end of [val]
  prval () = __assert () where {
    extern praxi __assert (): [b==(f==0)] void
  } // end of [prval]
in
  ans
end // end of [dlist_vt_is_beg]

implement{a}
dlist_vt_is_end
  {f,r} (xs) = let
  val+ DLISTcons
    (_, _, !p_xs1) = xs
  val next = dlist2ptr (!p_xs1)
  prval () = fold@ (xs)
  val [b:bool] ans = (
    if next > null then false else true
  ) : Bool // end of [val]
  prval () = __assert () where {
    extern praxi __assert (): [b==(r==1)] void
  } // end of [prval]
in
  ans
end // end of [dlist_vt_is_end]

implement{a}
rdlist_vt_is_beg
  {f,r} (xs) = dlist_vt_is_end {f,r} (xs)
// end of [rdlist_vt_is_beg]

implement{a}
rdlist_vt_is_end
  {f,r} (xs) = dlist_vt_is_beg {f,r} (xs)
// end of [rdlist_vt_is_end]

(* ****** ****** *)

implement{a}
dlist_vt_length
  {f,r} (xs) = let
  fun loop {r:nat}{r0:int} .<r>.
    (xs: !DLIST (a, r), res: int (r0)):<> int (r0+r) =
    case+ xs of
    | DLISTcons (_, _, !p_xs) => let
        val res = loop (!p_xs, res + 1); prval () = fold@ (xs)
      in
        res
      end // end of [DLISTcons]
    | DLISTnil () => (fold@ (xs); res)
  // end of [loop]
  prval () = lemma1_dlist_vt_params {a}{f,r} (xs)
in
  loop (xs, 0)
end // end of [dlist_vt_length]

implement{a}
rdlist_vt_length
  {f,r} (xs) = let
//
  fun loop {f:nat} .<f>.
    (prev: ptr, res: int):<> int = let
    val xs = __cast (prev) where {
      extern castfn __cast (p: ptr):<> [r:nat] DLIST (a, r)
    } // end of [val]
  in
    case+ xs of
    | DLISTcons
        (_, prev, _) => let
        prval () = fold@ {a} (xs)
        prval () = __assert () where {
          extern praxi __assert (): [f > 0] void
        } // end of [prval]
        prval () = __free (xs) where {
          extern praxi __free {r:int} (xs: DLIST (a, r)): void
        } // end of [prval]
      in
        loop {f-1} (prev, res + 1)
      end // end of [DLISTcons]
    | ~DLISTnil () => res
  end // end of [loop]
//
  prval () = lemma1_dlist_vt_params {a}{f,r} (xs)
//
  val res = (
    case+ xs of
    | DLISTcons (_, prev, _) => let
        prval () = fold@ (xs) in loop {f} (prev, 0)
      end // end of [DLISTcons]
    | DLISTnil () => (fold@ (xs); 0)
  ) : int // end of [val]
in
  __cast (res) where {
    extern castfn __cast (res: int):<> int (f)
  } // end of [__cast]
end // end of [rdlist_vt_length]

(* ****** ****** *)

implement{a}
dlist_vt_move
  {f,r} (xs) = let
  val+ DLISTcons (_, _, !p_xs1) = xs
  val xs1 = __copy (!p_xs1) where {
    extern castfn __copy (xs: !DLIST(a, r-1)):<> DLIST(a, r-1)
  } // end of [val]
  prval () = fold@ (xs)
  prval () = __free (xs) where {
    extern praxi __free (xs: DLIST (a, r)): void
  } // end of [prval]
in
  xs1 // : dlist_vt (a, f+1, r-1)
end // end of [dlist_vt_move]

implement{a}
rdlist_vt_move
  {f,r} (xs) = let
//
  prval () =
    lemma1_dlist_vt_params {a}{f,r} (xs)
  prval () = (
    sif r == 0 then
      lemma2_dlist_vt_params {a}{f} (xs)
    else () 
  ) : [r > 0] void
//
  val+ DLISTcons (_, prev, _) = xs
  prval () = fold@ (xs)
  prval () = __free (xs) where {
    extern praxi __free (xs: DLIST (a, r)): void
  } // end of [prval]
in
  __cast (prev) where {
    extern castfn __cast (p: ptr):<> DLIST(a, r+1)
  } // end of [__cast]
end // end of [rdlist_vt_move]

(* ****** ****** *)

implement{a}
dlist_vt_move_end
  {f,r} (xs) = let
  val isend = dlist_vt_is_end {f,r} (xs)
  prval () = lemma1_dlist_vt_params {a}{f,r} (xs)
in
  if isend then
    xs else dlist_vt_move_end {f+1,r-1} (dlist_vt_move {f,r} (xs))
  // end of [if]
end // end of [dlist_vt_move_end]

implement{a}
rdlist_vt_move_end
  {f,r} (xs) = let
  val isend = rdlist_vt_is_end {f,r} (xs)
  prval () = lemma1_dlist_vt_params {a}{f,r} (xs)
in
  if isend then
    xs else rdlist_vt_move_end {f-1,r+1} (rdlist_vt_move {f,r} (xs))
  // end of [if]
end // end of [rdlist_vt_move_end]

(* ****** ****** *)

implement{a}
dlist_vt_insert {f,r}
  (xs, x) = let
  val _xs = dlist2ptr (xs)
  val+ DLISTcons (_, _, !p_xs1) = xs
  val xs2 = dlist_vt_cons (x, !p_xs1)
  val+ DLISTcons (_, !p_prev, _) = xs2
  val () = !p_prev := _xs
  prval () = fold@ {a} (xs2)
  val () = !p_xs1 := xs2
  prval () = fold@ {a} (xs)
in
  xs
end // end of [dlist_vt_insert]

(* ****** ****** *)

implement{a}
dlist_vt_free {r} (xs) = let
  fun loop
    {r:nat} .<r>.
    (xs: DLIST (a, r)):<> void =
    case+ xs of
    | ~DLISTcons (_, _, xs) => loop (xs) | ~DLISTnil () => ()
  // end of [loop]
  prval () = lemma1_dlist_vt_params {a}{0,r} (xs)
in
  loop (xs)
end // end of [dlist_vt_free]

(* ****** ****** *)

implement{a}
dlist_vt_foreach_funenv
  {v}{vt}{f,r}{fe}
  (pfv | xs, f, env) = let
//
fun loop
  {f,r:int | r >= 0} .<r>. (
  pfv: !v
| xs: !dlist_vt (a, f, r)
, f: !(!v | &a, !vt) -<fe> void, env: !vt
) :<fe> void =
  case+ xs of
  | DLISTcons
      (!p_x, _, !p_xs1) => let
      val () = f (pfv | !p_x, env)
      val () = loop (pfv | !p_xs1, f, env)
      prval () = fold@ (xs)
    in
      // nothing
    end // end of [DLISTcons]
  | DLISTnil () => fold@ (xs)
// end of [loop]
//
prval () = lemma1_dlist_vt_params {a}{f,r} (xs)
//
in
  loop (pfv | xs, f, env)
end // end of [dlist_vt_foreach_funenv]

implement{a}
dlist_vt_foreach_fun
  {f,r} {fe:eff} (xs, f) = let
//
typedef fun0_t = (&a) -<fun,fe> void
typedef fun1_t = (!unit_v | &a, !ptr) -<fun,fe> void
//
val f = __cast (f) where { extern castfn __cast (f: fun0_t):<> fun1_t }
prval pf = unit_v ()
val () = dlist_vt_foreach_funenv<a> {unit_v} {ptr} (pf | xs, f, null)
prval unit_v () = pf
//
in
  // nothing
end // end of [dlist_vt_foreach_fun]

(* ****** ****** *)

implement{a}
rdlist_vt_foreach_funenv
  {v}{vt}{f,r}{fe}
  (pfv | xs, f, env) = let
//
fun loop {f:nat} .<f>. (
  pfv: !v
| prev: ptr, f: !(!v | &a, !vt) -<fe> void, env: !vt
) :<fe> void = let
  val xs = __cast (prev) where {
    extern castfn __cast (p: ptr):<> [r:nat] DLIST (a, r)
  } // end of [val]
in
  case+ xs of
  | DLISTcons
      (!p_x, prev, _) => let
      val () = f (pfv | !p_x, env)
      prval () = fold@ {a} (xs)
      prval () = __assert () where {
        extern praxi __assert (): [f > 0] void
      } // end of [prval]
      prval () = __free (xs) where {
        extern praxi __free {r:int} (xs: DLIST (a, r)): void
      } // end of [prval]
    in
      loop {f-1} (pfv | prev, f, env)
    end // end of [DLISTcons]
  | ~DLISTnil () => ()
end // end of [loop]
//
prval () = lemma1_dlist_vt_params {a}{f,r} (xs)
//
in
//
case+ xs of
| DLISTcons (_, prev, _) => let
    prval () = fold@ (xs) in loop {f} (pfv | prev, f, env)
  end // end of [DLISTcons]
| DLISTnil () => fold@ (xs)
//
end // end of [rdlist_vt_foreach_funenv]

implement{a}
rdlist_vt_foreach_fun
  {f,r} {fe:eff} (xs, f) = let
//
typedef fun0_t = (&a) -<fun,fe> void
typedef fun1_t = (!unit_v | &a, !ptr) -<fun,fe> void
//
val f = __cast (f) where { extern castfn __cast (f: fun0_t):<> fun1_t }
prval pf = unit_v ()
val () = rdlist_vt_foreach_funenv<a> {unit_v} {ptr} (pf | xs, f, null)
prval unit_v () = pf
//
in
  // nothing
end // end of [rdlist_vt_foreach_fun]

(* ****** ****** *)

(* end of [dlist_vt.dats] *)
