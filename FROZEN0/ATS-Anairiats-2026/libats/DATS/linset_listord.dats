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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
**
** A linear set implementation based on ordered lists
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: February 17, 2012
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

staload
_(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

staload "libats/SATS/linset_listord.sats"

(* ****** ****** *)
//
// a specialized version can be implemented on the spot
//
implement{a}
compare_elt_elt (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

assume
set_t0ype_viewtype (elt: t@ype) = List_vt (elt)

(* ****** ****** *)

implement{}
linset_make_nil () = list_vt_nil ()

implement{a}
linset_make_sing (x) = list_vt_sing (x)

(* ****** ****** *)

implement{a}
linset_size (xs) = size_of_int1 (list_vt_length (xs))

(* ****** ****** *)

implement{a}
linset_is_member
  (xs, x0, cmp) = let
//
fun loop
  {n:nat} .<n>. (
  xs: !list_vt (a, n)
) :<cloref> bool =
  case+ xs of
  | list_vt_cons
      (x, !p_xs) => let
      val sgn = compare_elt_elt<a> (x0, x, cmp)
    in
      if sgn < 0 then let
        prval () = fold@ {a} (xs) in false
      end else if sgn > 0 then let
        val ans = loop (!p_xs)
        prval () = fold@ {a} (xs)
      in
        ans
      end else let
        prval () = fold@ {a} (xs) in true // HX: x0 = x
      end (* end of [if] *)
    end // end of [list_vt_cons]
  | list_vt_nil () => (fold@ (xs); false)
// end of [loop]
in
  loop (xs)
end // end of [linset_is_member]

implement{a}
linset_isnot_member
  (xs, x0, cmp) = ~linset_is_member<a> (xs, x0, cmp)
// end of [linset_isnot_member]

(* ****** ****** *)

implement{a} linset_copy (xs) = list_vt_copy<a> (xs)
implement{a} linset_free (xs) = list_vt_free<a> (xs)

(* ****** ****** *)

implement{a}
linset_insert
  (xs, x0, cmp) = let
  fun ins {n:nat} .<n>. ( // tail-recursive
    xs: &list_vt (a, n) >> list_vt (a, n1)
  ) :<cloref> #[n1:nat | n <= n1; n1 <= n+1] bool =
    case+ xs of
    | list_vt_cons (x, !p_xs) => let
        val sgn = compare_elt_elt<a> (x0, x, cmp)
      in
        if sgn < 0 then let
          prval () = fold@ (xs)
          val () = xs := list_vt_cons (x0, xs)
        in
          false
        end else if sgn > 0 then let
          val res = ins (!p_xs); prval () = fold@ (xs) in res
        end else let // x0 = x
          prval () = fold@ (xs) in true // [x0] is already in [xs]
        end // end of [if]
      end (* end of [list_vt_cons] *)
    | ~list_vt_nil () => let
        val () = xs := list_vt_sing (x0) in false
      end // end of [list_vt_nil]
  // end of [ins]
in
  ins (xs)  
end // end of [linset_insert]

(* ****** ****** *)

implement{a}
linset_remove
  (xs, x0, cmp) = let
  fun rem {n:nat} .<n>. ( // tail-recursive
    xs: &list_vt (a, n) >> list_vt (a, n1)
  ) :<cloref> #[n1:nat | n1 <= n; n <= n1+1] bool =
    case+ xs of
    | list_vt_cons (x, !p_xs) => let
        val sgn = compare_elt_elt<a> (x0, x, cmp)
      in
        if sgn < 0 then let
          prval () = fold@ (xs) in false
        end else if sgn > 0 then let
          val res = rem (!p_xs); prval () = fold@ (xs) in res
        end else let // x0 = x
          val xs1 = !p_xs
          val () = free@ {a}{0} (xs)
          val () = xs := xs1
        in
          true // [x0] is removed from [xs]
        end // end of [if]
      end (* end of [list_vt_cons] *)
    | list_vt_nil () => let
        prval () = fold@ (xs) in false
      end // end of [list_vt_nil]
  // end of [rem]
in
  rem (xs)  
end // end of [linset_remove]

(* ****** ****** *)

(*
** By Brandon Barker
*)
implement{a}
linset_choose
  (xs, x0) = let
in
//
case+ xs of
| list_vt_cons
    (x, !p_xs) => let
    prval () = fold@ xs
    val () = x0 := x
    prval () = opt_some {a} (x0)
  in
    true
  end // end of [list_vt_cons]
| list_vt_nil () => let
    prval () = fold@ (xs)
    prval () = opt_none {a} (x0)
  in
    false
  end // end of [list_vt_nil]
//
end // end of [linset_choose]

implement{a}
linset_choose_out
  (xs0, x0) = let
in
//
case+ xs0 of
| ~list_vt_cons
    (x, xs) => let
    val () = x0 := x
    prval () = opt_some {a} (x0)
    val () = xs0 := xs
  in
    true
  end // end of [list_vt_cons]
| list_vt_nil () => let
    prval () = fold@ (xs0)
    prval () = opt_none {a} (x0)
  in
    false
  end // end of [list_vt_nil]
//
end // end of [linset_choose_out]

(* ****** ****** *)

implement{a}
linset_union
  (xs1, xs2, cmp) = let
//
viewtypedef res = List_vt (a)
fun loop
  {n1,n2:nat} .<n1+n2>. (
  xs1: list_vt (a, n1), xs2: list_vt (a, n2), res: &res? >> res
) :<cloref> void =
  case+ xs1 of
  | list_vt_cons (x1, !p_xs1) => (
    case+ xs2 of
    | list_vt_cons (x2, !p_xs2) => let
        val sgn = compare_elt_elt<a> (x1, x2, cmp)
      in
        if sgn < 0 then let
          val xs11 = !p_xs1
          prval () = fold@ {a} (xs2)
          val () = loop (xs11, xs2, !p_xs1)
          prval () = fold@ {a} (xs1)
        in
          res := xs1
        end else if sgn > 0 then let
          prval () = fold@ {a} (xs1)
          val xs21 = !p_xs2
          val () = loop (xs1, xs21, !p_xs2)
          prval () = fold@ (xs2)
        in
          res := xs2
        end else let // x1 = x2
          val xs11 = !p_xs1
          val xs21 = !p_xs2
          val () = free@ {a}{0} (xs2)
          val () = loop (xs11, xs21, !p_xs1)
          prval () = fold@ (xs1)
        in
          res := xs1
        end // end of [if]
      end // end of [list_vt_cons]
    | ~list_vt_nil () => (fold@ (xs1); res := xs1)
    ) // end of [list_vt_cons]
  | ~list_vt_nil () => (res := xs2)
// end of [loop]
var res: res // uninitialized
val () = loop (xs1, xs2, res)
in
  res
end // end of [linset_union]

(* ****** ****** *)

local
//
staload UN = "prelude/SATS/unsafe.sats"
//
in
//
implement{a}
linset_is_subset
  (xs1, xs2, cmp) = let
  fun loop
    {n1,n2:nat} .<n1+n2>. (
    xs1: list (a, n1), xs2: list (a, n2)
  ) :<cloref> bool =
    case+ xs1 of
    | list_cons (x1, xs11) => (
      case+ xs2 of
      | list_cons (x2, xs21) => let
          val sgn = compare_elt_elt<a> (x1, x2, cmp)
        in
          if sgn < 0 then false
          else if sgn > 0 then loop (xs1, xs21)
          else loop (xs11, xs21)
        end
      | list_nil () => false
      ) // end of [list_cons]
    | list_nil () => true
  // end of [loop]
in
  loop (
    $UN.castvwtp1 {List(a)} (xs1), $UN.castvwtp1 {List(a)} (xs2)
  ) // end of [loop]
end // end of [linset_is_subset]
//
implement{a}
linset_is_equal
  (xs1, xs2, cmp) = let
  fun loop
    {n1,n2:nat} .<n1+n2>. (
    xs1: list (a, n1), xs2: list (a, n2)
  ) :<cloref> bool = (
    case+ xs1 of
    | list_cons (x1, xs11) => (
      case+ xs2 of
      | list_cons (x2, xs21) => let
          val sgn = compare_elt_elt<a> (x1, x2, cmp)
        in
          if sgn = 0 then loop (xs11, xs21) else false
        end // end of [list_cons]
      | list_nil () => false
      ) // end of [list_cons]
    | list_nil () => (case+ xs2 of
      | list_cons _ => false | list_nil () => true
      ) // end of [list_nil]
  ) // end of [loop]
in
  loop (
    $UN.castvwtp1 {List(a)} (xs1), $UN.castvwtp1 {List(a)} (xs2)
  ) // end of [loop]
end // end of [linset_is_equal]
//
end // end of [local]

(* ****** ****** *)

implement{a}
linset_listize (xs) = list_vt_copy<a> (xs)

implement{a} linset_listize_free (xs) = xs

(* ****** ****** *)

(* end of [linset_listord.dats] *)
