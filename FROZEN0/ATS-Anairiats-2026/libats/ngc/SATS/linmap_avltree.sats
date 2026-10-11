(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
** A map implementation based on AVL trees
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by
**   Artyom Shalkhakov (artyom DOT shalkhakov AT gmail DOT com)
** Time: January, 2012
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

sortdef t0p = t@ype and vt0p = viewt@ype

(* ****** ****** *)

absview
avlnode_v (
  key:t@ype
, itm:viewt@ype+
, h:int
, ll:addr, lr:addr
, l:addr
) // end of [avlnode_v]

viewdef
avlnode_v (
  key:t0p, itm:vt0p, l0:addr
) = [h:int] [ll,lr:addr] avlnode_v (key, itm, h, ll, lr, l0)
// end of [avlnode_v]

prfun
avlnode_ptr_is_gtz
  {key:t0p;itm:vt0p} {h:int} {l,ll,lr:addr}
  (pf: !avlnode_v (key, itm, h, ll, lr, l)): [l > null] void
// end of [avlnode_ptr_is_gtz]

(* ****** ****** *)

typedef
avlnode_get_height_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,l0:addr} (
  !avlnode_v (key, itm, h, ll, lr, l0) | ptr l0
) -<fun> int h // end of [avlnode_get_height_type]
fun{key:t0p;itm:vt0p} avlnode_get_height : avlnode_get_height_type (key, itm) // specific

typedef
avlnode_set_height_type
  (key:t0p, itm:vt0p) = {h,h1:int} {ll,lr,l0:addr} (
  !avlnode_v (key, itm, h, ll, lr, l0) >> avlnode_v (key, itm, h1, ll, lr, l0)
| ptr l0, int h1
) -<fun> void // end of [avlnode_set_height_type]
fun{key:t0p;itm:vt0p} avlnode_set_height : avlnode_set_height_type (key, itm) // specific

typedef
avlnode_get_left_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,l0:addr} (
  !avlnode_v (key, itm, h, ll, lr, l0) | ptr l0
) -<fun> ptr ll // end of [avlnode_get_left_type]
fun{key:t0p;itm:vt0p} avlnode_get_left : avlnode_get_left_type (key, itm) // specific

typedef
avlnode_set_left_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,l0,ll1:addr} (
  !avlnode_v (key, itm, h, ll, lr, l0) >> avlnode_v (key, itm, h, ll1, lr, l0)
| ptr l0, ptr ll1
) -<fun> void // end of [avlnode_set_left_type]
fun{key:t0p;itm:vt0p} avlnode_set_left : avlnode_set_left_type (key, itm) // specific

typedef
avlnode_get_right_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,l0:addr} (
  !avlnode_v (key, itm, h, ll, lr, l0)
| ptr l0
) -<fun> ptr lr // end of [avlnode_get_right_type]
fun{key:t0p;itm:vt0p} avlnode_get_right : avlnode_get_right_type (key, itm) // specific

typedef
avlnode_set_right_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,l0,lr1:addr} (
  !avlnode_v (key, itm, h, ll, lr, l0) >> avlnode_v (key, itm, h, ll, lr1, l0)
| ptr l0, ptr lr1
) -<fun> void // end of [avlnode_set_right_type]
fun{key:t0p;itm:vt0p} avlnode_set_right : avlnode_set_right_type (key, itm) // specific

(* ****** ****** *)

typedef
avlnode_get_key_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,l0,l1:addr} (
  !avlnode_v (key, itm, h, ll, lr, l0)
| ptr l0
) -<fun> key // end of [avlnode_get_key_type]
fun{key:t0p;itm:vt0p} avlnode_get_key : avlnode_get_key_type (key, itm) // specific

typedef
avlnode_set_key_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,l0:addr} (
  !avlnode_v (key?, itm, h, ll, lr, l0) >> avlnode_v (key, itm, h, ll, lr, l0)
| ptr l0, key
) -<fun> void
fun{key:t0p;itm:vt0p} avlnode_set_key : avlnode_set_key_type (key, itm) // specific

(* ****** ****** *)

(*
//
// HX: this one requires that [itm] be the first field
//
prfun
avlnode_v_takeout_val
  {key:t0p;itm:vt0p} {h:int} {ll,lr,l0:addr}
  (pf: avlnode_v (key, itm, h, ll, lr, l0))
  : (itm @ l0, {itm:vt0p} itm @ l0 -<lin,prf> avlnode_v (key, itm, h, ll, lr, l0))
// end of [avlnode_v_takeout_val]
*)
typedef
avlnode_takeout_val_type
  (key:t0p, itm:vt0p) =
  {h:int} {ll,lr,l0:addr} (
  avlnode_v (key, itm, h, ll, lr, l0) | ptr l0
) -<fun> [l:addr] (
  itm @ l, {itm:vt0p} itm @ l -<lin,prf> avlnode_v (key, itm, h, ll, lr, l0) | ptr l
) // end of [avlnode_takeout_val_type]

fun{key:t0p;itm:vt0p} avlnode_takeout_val : avlnode_takeout_val_type (key, itm)

(* ****** ****** *)

typedef
avlnode_alloc_type
  (key:t0p, itm:vt0p) =
  () -<fun> [l:addr] [h:int] [ll,lr:addr] (
  option_v (avlnode_v (key?, itm?, h, ll, lr, l), l > null) | ptr l
) // end of [typedef]
fun{key:t0p;itm:vt0p} avlnode_alloc : avlnode_alloc_type (key, itm) // specific template

typedef
avlnode_free_type (key:t0p, itm:vt0p) =
  {h:int} {l,ll,lr:addr} (avlnode_v (key, itm?, h, ll, lr, l) | ptr l) -<fun> void
fun{key:t0p;itm:vt0p} avlnode_free : avlnode_free_type (key, itm) // specific template

(* ****** ****** *)

absviewtype
map_t0ype_viewt0ype_type (key:t@ype, itm:viewt@ype+)
stadef map = map_t0ype_viewt0ype_type

(* ****** ****** *)

typedef cmp (key:t0p) = (key, key) -<cloref> int

fun{key:t0p}
compare_key_key (x1: key, x2: key, cmp: cmp key):<> int

(* ****** ****** *)

fun{} linmap_make_nil {key:t0p;itm:vt0p} ():<> map (key, itm)

(* ****** ****** *)

fun{} linmap_is_nil {key:t0p;itm:vt0p} (m: !map (key, itm)):<> bool
fun{} linmap_isnot_nil {key:t0p;itm:vt0p} (m: !map (key, itm)):<> bool

(* ****** ****** *)
//
// HX: this function is O(n)-time and non-tail-recursive
//
fun{key:t0p;itm:vt0p}
linmap_size (m: !map (key, itm)):<> size_t
//
// HX: this function is O(1) // for gathering stats
fun{key:t0p;itm:vt0p} linmap_height (m: !map (key, itm)):<> Nat
//
(* ****** ****** *)

fun{key:t0p;itm:t0p}
linmap_search (
  m: !map (key, itm)
, k0: key, cmp: cmp key, res: &itm? >> opt (itm, b)
) :<> #[b:bool] bool b // end of [linmap_search]

(* ****** ****** *)
//
// AS:
// if [p0->key] occurs in [m], [p0] replaces the original node associated
// with [p0->key]
//
fun{key:t0p;itm:vt0p}
linmap_insert {l_at:addr} (
  pf_at: !avlnode_v (key, itm, l_at)
     >> option_v (avlnode_v (key, itm, l_at1), b)
| m: &map (key, itm), p0: &ptr l_at >> ptr l_at1, cmp: cmp key
) :<> #[b:bool;l_at1:addr] bool (b) // end of [linmap_insert]

(* ****** ****** *)

fun{key:t0p;itm:vt0p}
linmap_takeout (
  m: &map (key, itm)
, k0: key, cmp: cmp key
) :<> [l_at:addr] (option_v (avlnode_v (key, itm, l_at), l_at > null) | ptr l_at)
// end of [linmap_takeout]

fun{key:t0p;itm:t0p}
linmap_remove (m: &map (key, itm), k0: key, cmp: cmp key):<> bool
// end of [linmap_remove]

(* ****** ****** *)

fun{
key:t0p;itm:vt0p
} linmap_foreach_funenv
  {v:view} {vt:viewtype} (
  pf: !v
| m: !map (key, itm)
, f: (!v | key, &itm, !vt) -<fun> void
, env: !vt
) :<> void // end of [linmap_foreach_funenv]

fun{
key:t0p;itm:vt0p
} linmap_foreach_fun (
  m: !map (key, itm), f: (key, &itm) -<fun> void
) :<> void // end of [linmap_foreach_fun]

fun{
key:t0p;itm:vt0p
} linmap_foreach_vclo {v:view} (
  pf: !v
| m: !map (key, itm), f: &(!v | key, &itm) -<clo> void
) :<> void // end of [linmap_foreach_vclo]

(* ****** ****** *)

fun{
key:t0p;itm:vt0p
} linmap_rforeach_funenv
  {v:view} {vt:viewtype} (
  pf: !v
| m: !map (key, itm)
, f: (!v | key, &itm, !vt) -<fun> void
, env: !vt
) :<> void // end of [linmap_rforeach_funenv]

(* ****** ****** *)
//
// AS: clearing a map based on [foreach]
//
fun{
key:t0p;itm:vt0p
} linmap_clear_funenv
  {v:view} {vt:viewtype} (
  pf: !v
| m: !map (key, itm) >> map (key, itm?)
, f: (!v | key, &itm >> itm?, !vt) -<fun> void
, env: !vt
) :<> void // end of [linmap_clear_funenv]
//
(* ****** ****** *)
//
fun{key:t0p;itm:t0p}
linmap_free (m: map (key, itm)):<> void
//
// AS: frees the map if it is empty
//
fun{
key:t0p;itm:vt0p
} linmap_free_vt (
  m: !map (key, itm) >> opt (map (key, itm), b)
) :<> #[b:bool] bool b(*~freed*) // end of [linmap_free_vt]

(* ****** ****** *)

(* end of [linmap_avltree.sats] *)
