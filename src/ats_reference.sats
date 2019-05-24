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

// some common functions on references

(* ****** ****** *)

// implemented in [prelude/CATS/reference.cats]
fun ref_make_elt_tsz
  {a:viewt@ype} (x: &a >> a?, tsz: sizeof_t a):<> ref a
  = "atspre_ref_make_elt_tsz"

// implemented in [prelude/DATS/reference.dats]
fun{a:viewt@ype} ref_make_elt (x: a):<> ref a

// this is really an identity function; it is
// implemented in [prelude/CATS/reference.cats]
fun ref_make_view_ptr
  {a:viewt@ype} {l:addr} (pf: vbox (a @ l) | p: ptr l):<> ref a
  = "atspre_ref_make_view_ptr"

// implemented in [prelude/CATS/reference.cats]
fun ref_void_make ():<> ref void = "atspre_ref_void_make"

(* ****** ****** *)

// Operationally, it is the same as [ref_make_view_ptr]
fun refconst_make_view_ptr
  {a:t@ype} {l:addr} (pf: a @ l | p: ptr l):<> refconst a
  = "atspre_ref_make_view_ptr"

(* ****** ****** *)

// implemented in [prelude/DATS/reference.dats]
fun{a:t@ype} ref_get_elt (r: ref a):<!ref> a
  = "atspre_ref_get_elt"

// implemented in [prelude/DATS/reference.dats]
fun{a:t@ype} ref_set_elt (r: ref a, x: a):<!ref> void

(* ****** ****** *)

// implemented in [prelude/CATS/reference.cats]
fun ref_get_view_ptr
  {a:viewt@ype} (r: ref a):<> [l:addr] (vbox (a @ l) | ptr l)
  = "atspre_ref_get_view_ptr"

// implemented in [prelude/DATS/reference.dats]
fun{a:viewt@ype} ref_swap (r: ref a, x: &a):<!ref> void

(* ****** ****** *)

(* end of [ats_reference.sats] *)
