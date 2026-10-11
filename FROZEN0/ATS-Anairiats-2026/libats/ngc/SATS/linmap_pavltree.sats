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
pavlnode_v (
  key:t@ype
, itm:viewt@ype+
, h:int
, ll:addr, lr:addr
, lp:addr
, l:addr
) // end of [pavlnode_v]

viewdef
pavlnode_v (
  key:t0p, itm:vt0p, l0:addr
) = [h:int] [ll,lr,lp:addr] pavlnode_v (key, itm, h, ll, lr, lp, l0)
// end of [pavlnode_v]

prfun
pavlnode_ptr_is_gtz
  {key:t0p;itm:vt0p} {h:int} {l,ll,lr,lp:addr}
  (pf: !pavlnode_v (key, itm, h, ll, lr, lp, l)): [l > null] void
// end of [pavlnode_ptr_is_gtz]

(* ****** ****** *)

typedef
pavlnode_get_height_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0) | ptr l0
) -<fun> int h // end of [pavlnode_get_height_type]
fun{key:t0p;itm:vt0p} pavlnode_get_height : pavlnode_get_height_type (key, itm) // specific

typedef
pavlnode_set_height_type
  (key:t0p, itm:vt0p) = {h,h1:int} {ll,lr,lp,l0:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0) >> pavlnode_v (key, itm, h1, ll, lr, lp, l0)
| ptr l0, int h1
) -<fun> void // end of [pavlnode_set_height_type]
fun{key:t0p;itm:vt0p} pavlnode_set_height : pavlnode_set_height_type (key, itm) // specific

typedef
pavlnode_get_left_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0) | ptr l0
) -<fun> ptr ll // end of [pavlnode_get_left_type]
fun{key:t0p;itm:vt0p} pavlnode_get_left : pavlnode_get_left_type (key, itm) // specific

typedef
pavlnode_set_left_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0,ll1:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0) >> pavlnode_v (key, itm, h, ll1, lr, lp, l0)
| ptr l0, ptr ll1
) -<fun> void // end of [pavlnode_set_left_type]
fun{key:t0p;itm:vt0p} pavlnode_set_left : pavlnode_set_left_type (key, itm) // specific

typedef
pavlnode_get_right_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0)
| ptr l0
) -<fun> ptr lr // end of [pavlnode_get_right_type]
fun{key:t0p;itm:vt0p} pavlnode_get_right : pavlnode_get_right_type (key, itm) // specific

typedef
pavlnode_set_right_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0,lr1:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0) >> pavlnode_v (key, itm, h, ll, lr1, lp, l0)
| ptr l0, ptr lr1
) -<fun> void // end of [pavlnode_set_right_type]
fun{key:t0p;itm:vt0p} pavlnode_set_right : pavlnode_set_right_type (key, itm) // specific

typedef
pavlnode_get_parent_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0)
| ptr l0
) -<fun> ptr lp // end of [pavlnode_get_parent_type]
fun{key:t0p;itm:vt0p} pavlnode_get_parent : pavlnode_get_parent_type (key, itm) // specific

typedef
pavlnode_set_parent_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0,lp1:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0) >> pavlnode_v (key, itm, h, ll, lr, lp1, l0)
| ptr l0, ptr lp1
) -<fun> void // end of [pavlnode_set_parent_type]
fun{key:t0p;itm:vt0p} pavlnode_set_parent : pavlnode_set_parent_type (key, itm) // specific

(* ****** ****** *)

typedef
pavlnode_get_key_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0:addr} (
  !pavlnode_v (key, itm, h, ll, lr, lp, l0)
| ptr l0
) -<fun> key // end of [pavlnode_get_key_type]
fun{key:t0p;itm:vt0p} pavlnode_get_key : pavlnode_get_key_type (key, itm) // specific

typedef
pavlnode_set_key_type
  (key:t0p, itm:vt0p) = {h:int} {ll,lr,lp,l0:addr} (
  !pavlnode_v (key?, itm, h, ll, lr, lp, l0) >> pavlnode_v (key, itm, h, ll, lr, lp, l0)
| ptr l0, key
) -<fun> void
fun{key:t0p;itm:vt0p} pavlnode_set_key : pavlnode_set_key_type (key, itm) // specific

(* ****** ****** *)

typedef
pavlnode_takeout_val_type
  (key:t0p, itm:vt0p) =
  {h:int} {ll,lr,lp,l0:addr} (
  pavlnode_v (key, itm, h, ll, lr, lp, l0) | ptr l0
) -<fun> [l:addr] (
  itm @ l, {itm:vt0p} itm @ l -<lin,prf> pavlnode_v (key, itm, h, ll, lr, lp, l0) | ptr l
) // end of [pavlnode_takeout_val_type]

fun{key:t0p;itm:vt0p} pavlnode_takeout_val : pavlnode_takeout_val_type (key, itm)

(* ****** ****** *)

typedef
pavlnode_alloc_type
  (key:t0p, itm:vt0p) =
  () -<fun> [l:addr] [h:int] [ll,lr,lp:addr] (
  option_v (pavlnode_v (key?, itm?, h, ll, lr, lp, l), l > null) | ptr l
) // end of [typedef]
fun{key:t0p;itm:vt0p} pavlnode_alloc : pavlnode_alloc_type (key, itm) // specific template

typedef
pavlnode_free_type (key:t0p, itm:vt0p) =
  {h:int} {l,ll,lr,lp:addr} (pavlnode_v (key, itm?, h, ll, lr, lp, l) | ptr l) -<fun> void
fun{key:t0p;itm:vt0p} pavlnode_free : pavlnode_free_type (key, itm) // specific template

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
  pf_at: !pavlnode_v (key, itm, l_at)
     >> option_v (pavlnode_v (key, itm, l_at1), b)
| m: &map (key, itm), p0: &ptr l_at >> ptr l_at1, cmp: cmp key
) :<> #[b:bool;l_at1:addr] bool (b) // end of [linmap_insert]

(* ****** ****** *)

fun{key:t0p;itm:vt0p}
linmap_takeout (
  m: &map (key, itm)
, k0: key, cmp: cmp key
) :<> [l_at:addr] (option_v (pavlnode_v (key, itm, l_at), l_at > null) | ptr l_at)
// end of [linmap_takeout]

fun{key:t0p;itm:t0p}
linmap_remove (m: &map (key, itm), k0: key, cmp: cmp key):<> bool
// end of [linmap_remove]

(* ****** ****** *)

(*
// AS: enumerating elements of linear map
// TODO: provide an implementation

absviewtype enum_t0ype_viewt0ype_type (
  key:t@ype, itm:viewt@ype+, nf:int, nr:int, l:addr
) = ptr
stadef enum = enum_t0ype_viewt0ype_type

// start enumeration from the least element
fun{key:t0p;itm:vt0p} enum_first {l:addr} (
  pf: map (key, itm) @ l
| p: ptr l
) :<> [nr:nat] enum (key, itm, 0, nr, l)

// start enumeration from the greatest element
fun{key:t0p;itm:vt0p} enum_last {l:addr} (
  pf: map (key, itm) @ l
| p: ptr l
) :<> [nf:nat] enum (key, itm, nf, 0, l)

// navigate to the successor
fun{key:t0p;itm:vt0p} enum_succ {nf:int;nr:pos} {l:addr} (
  e: enum (key, itm, nf, nr, l)
) :<> enum (key, itm, nf+1, nr-1, l)

// navigate to the predecessor
fun{key:t0p;itm:vt0p} enum_pred {nf:pos;nr:int} {l:addr} (
  e: enum (key, itm, nf, nr, l)
) :<> enum (key, itm, nf-1, nr+1, l)

fun{key:t0p;itm:vt0p}
enum_is_at_end {nf,nr:int | nr > 0} {l:addr} (
  e: !enum (key, itm, nf, nr, l)
) :<> bool (nr <= 1)
// end of [enum_is_at_end]

fun{key:t0p;itm:vt0p}
enum_isnot_at_end {nf,nr:int | nr > 0} {l:addr} (
  e: !enum (key, itm, nf, nr, l)
) :<> bool (nr >= 2)
// end of [enum_isnot_at_end]

fun{key:t0p;itm:vt0p}
enum_is_at_beg {nf,nr:int | nr > 0} {l:addr} (
  e: !enum (key, itm, nf, nr, l)
) :<> bool (nf <= 0)
// end of [enum_is_at_beg]

fun{key:t0p;itm:vt0p}
enum_isnot_at_beg {nf,nr:int | nr > 0} {l:addr} (
  e: !enum (key, itm, nf, nr, l)
) :<> bool (nf >= 1)
// end of [enum_isnot_at_beg]

fun{key:t0p;itm:vt0p}
enum_app_funenv
  {v:view} {vt:viewtype} {nf,nr:int | nr > 0} {l:addr} (
  pfv: !v
| e: !enum (key, itm, nf, nr, l)
, f: (!v | key, &itm, !vt) -<fun> void
, env: !vt
) :<> void // end of [enum_app_funenv]

fun{key:t0p;itm:vt0p}
enum_app_fun
  {nf,nr:int | nr > 0} {l:addr} (
  e: !enum (key, itm, nf, nr, l)
, f: (key, &itm) -<fun> void
) :<> void // end of [enum_app_fun]

prfun enum_free {key:t0p;itm:vt0p} {nf,nr:int} {l:addr} (
  x: enum (key, itm, nf, nr, l)
) :<> map (key, itm) @ l

*)

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
// AS: tail-recursive traversal functions (using parent pointers)

fun{
key:t0p;itm:vt0p
} linmap_foreach_fun_iter (
  m: !map (key, itm), f: (key, &itm) -<fun> void
) :<> void // end of [linmap_foreach_fun_iter]

fun{
key:t0p;itm:vt0p
} linmap_rforeach_fun_iter (
  m: !map (key, itm), f: (key, &itm) -<fun> void
) :<> void // end of [linmap_rforeach_fun_iter]

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
