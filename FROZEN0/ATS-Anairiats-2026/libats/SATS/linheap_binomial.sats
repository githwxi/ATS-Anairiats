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

(* Author: Hongwei Xi *)
(* Authoremail: hwxi AT cs DOT bu DOT edu *)
(* Start time: November, 2011 *)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

absviewtype
heap_viewt0ype_viewtype (a:viewt@ype+)
stadef heap = heap_viewt0ype_viewtype

(* ****** ****** *)

sortdef vt0p = viewt@ype

(* ****** ****** *)
//
typedef cmp (a:vt0p) = (&a, &a) -<cloref> int
//
fun{a:vt0p}
compare_elt_elt (x1: &a, x2: &a, cmp: cmp a):<> int
//
(* ****** ****** *)

fun{} linheap_make_nil {a:vt0p} ():<> heap (a)

(* ****** ****** *)

fun{a:vt0p} linheap_size (hp: !heap a): size_t

(* ****** ****** *)

fun linheap_is_empty {a:vt0p} (hp: !heap (a)):<> bool
fun linheap_isnot_empty {a:vt0p} (hp: !heap (a)):<> bool

(* ****** ****** *)

fun{a:vt0p}
linheap_insert (
  hp: &heap (a), x: a, cmp: cmp a
) :<> void // end of [linheap_insert]

(* ****** ****** *)

fun{a:t@ype}
linheap_getmin (
  hp: !heap (a), cmp: cmp a, res: &a? >> opt (a, b)
) :<> #[b:bool] bool b // end of [linheap_getmin]

fun{a:vt0p}
linheap_getmin_ref (hp: !heap (a), cmp: cmp a):<> ptr

(* ****** ****** *)

fun{a:vt0p}
linheap_delmin (
  hp: &heap (a), cmp: cmp a, res: &a? >> opt (a, b)
) :<> #[b:bool] bool b // end of [linheap_delmin]

(* ****** ****** *)

fun{a:vt0p}
linheap_merge (
  hp1: heap (a), hp2: heap (a), cmp: cmp a
) :<> heap (a) // end of [linheap_merge]

(* ****** ****** *)

fun{a:t0p}
linheap_free (hp: heap (a)): void

fun{a:vt0p}
linheap_free_vt (
  hp: !heap(a) >> opt (heap(a), b)
) :<> #[b:bool] bool b(*~freed*) // end of [linheap_free_vt]

(* ****** ****** *)

(* end of [linheap_binomial.sats] *)
