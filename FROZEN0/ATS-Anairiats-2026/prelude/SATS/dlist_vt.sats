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

sortdef tp = type
sortdef vtp = viewtype
sortdef t0p = t@ype
sortdef vt0p = viewt@ype

(* ****** ****** *)

(*
**
** HX-2012-02-29:
** dlist_vt (a, f, r) means that there are f elements in
** front of the current one while r-1 elements after it. So the
** total number of elements is f+r. If f=r=0, then the list is
** empty.
**
*)
absviewtype // f: front; r: rear
dlist_viewt0ype_int_int_viewtype (a: viewt@ype+, f: int, r: int)
stadef dlist_vt = dlist_viewt0ype_int_int_viewtype

(* ****** ****** *)

praxi
lemma1_dlist_vt_params {a:vt0p}
  {f,r:int} (xs: !dlist_vt (a, f, r)): [f >= 0;r >= 0] void
// end of [lemma_dlist_vt_params]

praxi
lemma2_dlist_vt_params
  {a:vt0p} {f:int} (xs: !dlist_vt (a, f, 0)): [f == 0] void
// end of [lemma2_dlist_vt_params]

(* ****** ****** *)

fun{a:vt0p}
dlist_vt_nil ():<> dlist_vt (a, 0, 0)

fun{a:vt0p}
dlist_vt_sing (x: a):<> dlist_vt (a, 0, 1)

fun{a:vt0p}
dlist_vt_cons {r:int}
  (x: a, xs: dlist_vt (a, 0, r)):<> dlist_vt (a, 0, r+1)

fun{a:vt0p}
dlist_vt_snoc {f:int}
  (xs: dlist_vt (a, f, 1), x: a):<> dlist_vt (a, f+1, 1)

(* ****** ****** *)

fun{a:vt0p}
dlist_vt_is_beg
  {f,r:int | r > 0}
  (xs: !dlist_vt (a, f, r)):<> bool (f==0)
// end of [dlist_vt_is_beg]
fun{a:vt0p}
dlist_vt_is_end
  {f,r:int | r > 0}
  (xs: !dlist_vt (a, f, r)):<> bool (r==1)
// end of [dlist_vt_is_end]

fun{a:vt0p}
rdlist_vt_is_beg
  {f,r:int | r > 0}
  (xs: !dlist_vt (a, f, r)):<> bool (r==1)
// end of [rdlist_vt_is_end]
fun{a:vt0p}
rdlist_vt_is_end
  {f,r:int | r > 0}
  (xs: !dlist_vt (a, f, r)):<> bool (f==0)
// end of [rdlist_vt_is_end]

(* ****** ****** *)

fun{a:t0p}
dlist_vt_get
  {f,r:int | r > 0} (xs: !dlist_vt (a, f, r)): a
// end of [dlist_vt_get]
fun{a:t0p}
dlist_vt_set
  {f,r:int | r > 0} (xs: !dlist_vt (a, f, r), x: a): void
// end of [dlist_vt_set]

(* ****** ****** *)

fun{a:vt0p}
dlist_vt_length
  {f,r:int} (xs: !dlist_vt (a, f, r)):<> int (r)
fun{a:vt0p}
rdlist_vt_length
  {f,r:int} (xs: !dlist_vt (a, f, r)):<> int (f)

(* ****** ****** *)

fun{a:vt0p}
dlist_vt_move
  {f,r:int | r > 1}
  (xs: dlist_vt (a, f, r)):<> dlist_vt (a, f+1, r-1)
fun{a:vt0p}
rdlist_vt_move
  {f,r:int | f > 0}
  (xs: dlist_vt (a, f, r)):<> dlist_vt (a, f-1, r+1)

(* ****** ****** *)

fun{a:vt0p}
dlist_vt_move_end
  {f,r:int | r > 0}
  (xs: dlist_vt (a, f, r)):<> dlist_vt (a, f+r-1, 1)
// end of [dlist_vt_move_end]
fun{a:vt0p}
rdlist_vt_move_end
  {f,r:int | r > 0}
  (xs: dlist_vt (a, f, r)):<> dlist_vt (a, 0, f+r)
// end of [rdlist_vt_move_end]

(* ****** ****** *)

fun{a:vt0p}
dlist_vt_insert
  {f,r:int | r > 0}
  (xs: dlist_vt (a, f, r), x: a):<> dlist_vt (a, f, r+1)
// end of [dlist_vt_insert]

(* ****** ****** *)

fun{a:t@ype}
dlist_vt_free {r:int} (xs: dlist_vt (a, 0, r)):<> void

(* ****** ****** *)

fun{a:vt0p}
dlist_vt_foreach_funenv
  {v:view}{vt:vtp}{f,r:int}{fe:eff} (
  pf: !v
| xs: !dlist_vt (a, f, r)
, f: !(!v | &a, !vt) -<fe> void, env: !vt
) :<fe> void // end of [dlist_vt_foreach_funenv]

fun{a:vt0p}
dlist_vt_foreach_fun
  {f,r:int} {fe:eff}
  (xs: !dlist_vt (a, f, r), f: (&a) -<fun,fe> void):<fe> void
// end of [dlist_vt_foreach_fun]

(* ****** ****** *)

fun{a:vt0p}
rdlist_vt_foreach_funenv
  {v:view}{vt:vtp}{f,r:int}{fe:eff} (
  pf: !v
| xs: !dlist_vt (a, f, r)
, f: !(!v | &a, !vt) -<fe> void
, env: !vt
) :<fe> void // end of [rdlist_vt_foreach_funenv]

fun{a:vt0p}
rdlist_vt_foreach_fun
  {f,r:int} {fe:eff}
  (xs: !dlist_vt (a, f, r), f: (&a) -<fun,fe> void):<fe> void
// end of [rdlist_vt_foreach_fun]

(* ****** ****** *)

(* end of [dlist_vt.sats] *)
