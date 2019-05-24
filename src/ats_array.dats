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
// March 2008

(* ****** ****** *)

staload "ats_array.sats"

(* ****** ****** *)

implement{a} array_ptr_alloc
  (asz) = array_ptr_alloc_tsz {a} (asz, sizeof<a>)
// end of ...

(* ****** ****** *)

implement{a}
array_ptr_initialize_elt (A0, n0, x0) = let
  fun aux {n:nat} {l:addr} .<n>.
    (pf: array_v (a?, n, l) | p: ptr l, n: int n, x: a)
    :<> (array_v (a, n, l) | void) =
    if n > 0 then let
      prval (pf1, pf2) = array_v_uncons {a?} (pf)
      val () = !p := x
      val (pf2 | ()) = aux (pf2 | p + sizeof<a>, n - 1, x)
    in
      (array_v_cons {a} (pf1, pf2) | ())
    end else let
      prval () = array_v_unnil (pf) in (array_v_nil {a} () | ())
    end // end of [if]
  prval pf = view@ A0
  val (pf | ()) = aux (pf | &A0, n0, x0)
  prval () = view@ A0 := pf
in
  // nothing
end // end of [array_ptr_initialize_elt]
    
(* ****** ****** *)

implement{a}
array_ptr_make_elt (n, x) = let
  val (pf_gc, pf | p) = array_ptr_alloc_tsz {a} (n, sizeof<a>)
  val () = array_ptr_initialize_elt<a> (!p, n, x)
in
  (pf_gc, pf | p)
end // end of [array_ptr_make_elt]

(* ****** ****** *)

implement{a}
array_ptr_initialize_lst (A0, xs0) = let
  fun aux {n:nat} {l:addr} .<n>.
    (pf: array_v (a?, n, l) | p: ptr l, xs: list (a, n))
    :<> (array_v (a, n, l) | void) = begin case+ xs of
    | list_cons (x, xs) => let
        prval (pf1, pf2) = array_v_uncons {a?} (pf)
        val () = !p := x
        val (pf2 | ans) = aux (pf2 | p+sizeof<a>, xs)
      in
        (array_v_cons {a} (pf1, pf2) | ans)
      end // end of [list_cons]
    | list_nil () => let
        prval () = array_v_unnil {a?} (pf) in (array_v_nil {a} () | ())
      end // end of [list_nil]
  end // end of [aux]
  val (pf | ()) = aux (view@ A0 | &A0, xs0)
in
  view@ A0 := pf
end // end of [array_ptr_initialize_lst]

implement{a}
array_ptr_make_lst (n, xs) = let
  val (pf_gc, pf | p) = array_ptr_alloc_tsz {a} (n, sizeof<a>)
  val () = array_ptr_initialize_lst<a> (!p, xs)
in
  (pf_gc, pf | p)
end // end of [array_ptr_make_lst]

(* ****** ****** *)

implement{a} // [xs0] is freed
array_ptr_initialize_lst_vt (A0, xs0) = let
  fun aux {n:nat} {l:addr} .<n>. (
      pf: array_v (a?, n, l)
    | p: ptr l, xs: list_vt (a, n)
    ) :<> (array_v (a, n, l) | void) = begin case+ xs of
    | ~list_vt_cons (x, xs) => let
        prval (pf1, pf2) = array_v_uncons {a?} (pf)
        val () = !p := x
        val (pf2 | ans) = aux (pf2 | p+sizeof<a>, xs)
      in
        (array_v_cons {a} (pf1, pf2) | ans)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => let
        prval () = array_v_unnil {a?} (pf) in (array_v_nil {a} () | ())
      end // end of [if]
  end // end of [aux]    
  val (pf | ()) = aux (view@ A0 | &A0, xs0)
in
  view@ A0 := pf
end // end of [array_ptr_initialize_lst_vt]

implement{a}
array_ptr_make_lst_vt (n, xs) = let
  val (pf_gc, pf | p) = array_ptr_alloc_tsz {a} (n, sizeof<a>)
  val () = array_ptr_initialize_lst_vt<a> (!p, xs)
in
  (pf_gc, pf | p)
end // end of [array_ptr_make_lst_vt]

(* ****** ****** *)

%{$

ats_ptr_type
ats_array_ptr_alloc_tsz (
  ats_int_type n, ats_size_type tsz
) {
  return ATS_MALLOC(n * tsz) ; // uninitialized
} /* end of [ats_array_ptr_alloc_tsz] */

ats_void_type
ats_array_ptr_free
  (ats_ptr_type base) { ATS_FREE(base); return ; }
// end of [ats_array_ptr_free]

%} // end of [%{$]

(* ****** ****** *)

(* end of [ats_array.sats] *)
