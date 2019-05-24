(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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

%{#
#include "contrib/linux/linux/CATS/slab.cats"
%} // end of [%{#]

(* ****** ****** *)

staload GFP = "contrib/linux/linux/SATS/gfp.sats"
typedef gfp_t = $GFP.gfp_t

(* ****** ****** *)

absview kfree_v (n:int, l:addr)

(* ****** ****** *)

dataview
kmalloc_v (n:int, addr) =
  | {l:agz}
    kmalloc_v_succ (n, l) of (kfree_v (n, l), b0ytes n @ l)
  | kmalloc_v_fail (n, null) of ()
// end of [kmalloc_v]

fun kmalloc
  {n:nat} (
  n: size_t n, flags: gfp_t
) :<> [l:addr] (
  kmalloc_v (n, l) | ptr l
) = "mac#atsctrb_linux_kmalloc"

(* ****** ****** *)

fun kfree
  {n:nat} {l:addr} (
  pf1: kfree_v (n, l)
, pf2: b0ytes (n) @ l | p: ptr l
) : void = "mac#atsctrb_linux_kfree" // end of [kfree]

(* ****** ****** *)

(*
** Flags to pass to kmem_cache_create().
** The ones marked DEBUG are only valid if CONFIG_SLAB_DEBUG is set.
*)
macdef SLAB_DEBUG_FREE = $extval (ulint, "SLAB_DEBUG_FREE")
macdef SLAB_RED_ZONE = $extval (ulint, "SLAB_RED_ZONE")
macdef SLAB_POISON = $extval (ulint, "SLAB_POISON")
macdef SLAB_HWCACHE_ALIGN = $extval (ulint, "SLAB_HWCACHE_ALIGN")
macdef SLAB_CACHE_DMA = $extval (ulint, "SLAB_CACHE_DMA")
macdef SLAB_STORE_USER = $extval (ulint, "SLAB_STORE_USER")
macdef SLAB_PANIC = $extval (ulint, "SLAB_PANIC")
macdef SLAB_DESTROY_BY_RCU = $extval (ulint, "SLAB_DESTROY_BY_RCU")
macdef SLAB_MEM_SPREAD = $extval (ulint, "SLAB_MEM_SPREAD")
macdef SLAB_TRACE = $extval (ulint, "SLAB_TRACE")
macdef SLAB_DEBUG_OBJECTS = $extval (ulint, "SLAB_DEBUG_OBJECTS")
macdef SLAB_NOLEAKTRACE = $extval (ulint, "SLAB_NOLEAKTRACE")
macdef SLAB_NOTRACK = $extval (ulint, "SLAB_NOTRACK")
macdef SLAB_FAILSLAB = $extval (ulint, "SLAB_FAILSLAB")
macdef SLAB_RECLAIM_ACCOUNT = $extval (ulint, "SLAB_RECLAIM_ACCOUNT")
macdef SLAB_TEMPORARY = $extval (ulint, "SLAB_TEMPORARY")

(* ****** ****** *)

(*
viewtypedef
kmem_cache (n:int) =
$extype_struct
"kmem_cache_struct" of {
  _rest= undefined_vt
} // end of [kmem_cache_struct]
*)
absviewt@ype
kmem_cache_struct (n:int) = $extype"kmem_cache_struct"
stadef kmem_cache = kmem_cache_struct

fun slab_is_available (): int
  = "mac#atsctrb_linux_slab_is_available"
// end of [fun]

fun kmem_cache_size
  {n:nat} (
  cache: &kmem_cache (n)
) : uint (n)
  = "mac#atsctrb_linux_kmem_cache_size"
// end of [fun]

fun kmem_cache_name
  {n:int} (
  cache: &kmem_cache (n)
) : string = "mac#atsctrb_linux_kmem_cache_name"

(* ****** ****** *)

fun kmem_cache_destroy
  {n:int} {l:addr} (
  pf: kmem_cache (n) @ l | p: ptr l
) : void = "mac#atsctrb_linux_kmem_cache_destroy"
// end of [fun]

(* ****** ****** *)

absview kfree_cache_v (l:addr)

dataview
kmem_cache_alloc_v (n: int, addr) =
  | {l:agz}
    kmem_cache_alloc_v_succ (n, l) of (kfree_cache_v l, b0ytes (n) @ l)
  | keme_cache_alloc_v_fail (n, null) of ()
// end of [kmem_cache_alloc_v]

fun kmem_cache_alloc
  {n:nat} (
  cache: &kmem_cache n, flags: gfp_t
) : [l:agez] (
  kmem_cache_alloc_v (n, l) | ptr l
) = "mac#atsctrb_linux_kmem_cache_alloc"

fun kmem_cache_free
  {n:int} {l:addr} (
  pf: kfree_cache_v l
| cache: &kmem_cache n, p: ptr l
) : void = "mac#atsctrb_linux_kmem_cache_free"

(* ****** ****** *)

(* end of [slab.sats] *)
