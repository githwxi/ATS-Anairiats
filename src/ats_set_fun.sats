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
// Time: October 2007

(* ****** ****** *)

abstype set_t (elt: t@ype+)

typedef ord (a:t@ype) = (a, a) -<fun> Sgn

val set_nil : {a:t@ype} set_t (a)

fun{a:t@ype} set_member (_: set_t a, _: a, _: ord a): bool

fun{a:t@ype} set_insert (_: set_t a, _: a, _: ord a): set_t a
fun{a:t@ype} set_remove (_: set_t a, _: a, _: ord a): set_t a

fun{a:t@ype} set_inter (_: set_t a, _: set_t a, _: ord a): set_t a
fun{a:t@ype} set_union (_: set_t a, _: set_t a, _: ord a): set_t a

(* ****** ****** *)

fun{a:t@ype} set_foreach_main {v:view} {vt:viewtype} {f:eff}
  (pf: !v | xs: set_t a, f: (!v | a, !vt) -<f> void, env: !vt):<f> void

fun{a:t@ype} set_foreach_cloptr {f:eff}
  (xs: set_t a, f: !(a -<cloptr,f> void)):<f> void

(* ****** ****** *)

(* end of [ats_set_fun.sats] *)
