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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/pointer.dats"

(* ****** ****** *)

staload "libats/SATS/refcount.sats"

(* ****** ****** *)

implement{a}
refcount_make
  (x) = r where {
  viewtypedef VT = @(uint, a)
  val [l:addr]
    (pfgc, pfat | p) = ptr_alloc<VT> ()
  val () = p->0 := 1u and () = p->1 := x
  val r = __cast (pfgc, pfat | p) where {
    extern castfn __cast
      (pf1: free_gc_v (VT?, l), pf2: VT@l | p: ptr l):<> nref(a)
    // end of [extern]
  } // end of [val]
} // end of [refcount]

(* ****** ****** *)

implement{a}
refcount_ref
  (r) = r1 where {
  viewtypedef VT = @(uint, a)
  val (pfat, fpf | p) = __cast (r) where {
    extern castfn __cast
      (r: !nref (a)):<> [l:addr] (VT@l, VT@l -<lin,prf> void | ptr l)
    // end of [extern]
  } // end of [val]
  val () = p->0 := p->0 + 1u
  prval () = fpf (pfat)
  val r1 = __ref (r) where {
    extern castfn __ref (r: !nref a):<> nref a
  } // end of [val]
} // end of [refcount_ref]

(* ****** ****** *)

implement{a}
refcount_unref
  (r, x) = let
//
viewtypedef VT = @(uint, a)
val [l:addr] p = __cast (r) where {
  extern castfn __cast (r: !nref (a)):<> [l:addr] ptr (l)
  // end of [extern]
} // end of [val]
prval (pfat, fpf) = __assert () where {
  extern praxi __assert (): (VT@l, VT@l -<lin,prf> void)
} // end of [prval]
val n = p->0
prval () = fpf (pfat)
//
in
//
if n > 1u then let
  prval (pfat, fpf) = __assert () where {
    extern praxi __assert (): (VT@l, VT@l -<lin,prf> void)
  } // end of [prval]
  val () = p->0 := n - 1u
  prval () = fpf (pfat)
  prval () = opt_none {a} (x)
  prval () = __unref (r) where {
    extern prfun __unref (r: nref (a)): void
  } // end of [prval]
in
  false // refcount is still positive
end else let
  prval (pfat, fpf) = __assert () where {
    extern praxi __assert (): (VT@l, (VT?)@l -<lin,prf> void)
  } // end of [prval]
  val () = x := p->1
  prval () = fpf (pfat)
  prval () = opt_some {a} (x)
  val () = __free (r) where {
    extern fun __free (r: nref (a)):<> void = "ats_free_gc"
  } // end of [prval]
in
  true // refcount has reached 0
end // end of [if]
//
end // end of [refcount_unref]

implement{a}
refcount_unref_fun (r, f) = let
  var x: a?
  val res = refcount_unref (r, x)
in
  if res then let
    val () = opt_unsome {a} (x)
  in
    f (x)
  end else let
    val () = opt_unnone {a} (x)
  in
    // nothing
  end // end of [if]
end // end of [refcount_unref_fun]

(* ****** ****** *)

implement{a}
refcount_get_count (r) = n where {
  viewtypedef VT = @(uint, a)
//
  val (pfat, fpf | p) = __cast (r) where {
    extern castfn __cast
      (r: !nref (a)):<> [l:addr] (VT@l, VT@l -<lin,prf> void | ptr l)
    // end of [extern]
  } // end of [val]
  val n = p->0
  prval () = fpf (pfat)
//
} // end of [refcount_get_count]

(* ****** ****** *)

implement{a}
refcount_takeout
  (r) = (pf1at | p1) where {
  viewtypedef VT = @(uint, a)
//
  val (pfat, fpf | p) = __cast (r) where {
    extern castfn __cast
      (r: !nref (a)):<> [l:addr] (VT@l, VT@l -<lin,prf> void | ptr l)
    // end of [extern]
  } // end of [val]
//
  val [l1:addr] p1 = &(p->1) : Ptr
//
  prval () = fpf (pfat)
//
  prval pf1at = __assert (r) where {
    extern praxi __assert (r: !nref (a) >> nrefout (a, l1)): a @ l1
  } // end of [prval]
} // end of [refcount_takeout]

(* ****** ****** *)

(* end of [refcount.dats] *)
