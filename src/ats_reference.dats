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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)
// Time: month? 2007

(* ****** ****** *)

// some built-in static constants for reference operations

(* ****** ****** *)

staload "ats_reference.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

(*
assume ref_viewt0ype_type
  (a:viewt@ype) = [l:addr] @(vbox (a @ l) | ptr l)
// end of [ref_viewt0ype_type]
*)

(* ****** ****** *)

implement{a} ref_make_elt (x) = begin
  let var x = x in ref_make_elt_tsz {a} (x, sizeof<a>) end
end // end of [ref_make_elt]

(* ****** ****** *)

implement{a} ref_get_elt (r) = !r
implement{a} ref_set_elt (r, x) = (!r := x)

(* ****** ****** *)

implement{a} ref_swap (r, x) = let
  val (vbox pf | p) = ref_get_view_ptr r
  val tmp = !p
in
  !p := x; x := tmp
end // end of [ref_swap]

(* ****** ****** *)

(* end of [ats_reference.dats] *)
