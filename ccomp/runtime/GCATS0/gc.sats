(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

#include "gc.hats"

(* ****** ****** *)

#include "gc.hats"

absviewt@ype freeitm = $extype "freeitm"
absviewt@ype freelst (length: int) = $extype "freelst"
viewtypedef Freelst = [n:nat] freelst n

(* ****** ****** *)

fun gcats0_malloc_err {n:nat}
  (n: int n): [l:addr] (option_v (bytes_v (n, l), l <> null) | ptr l)
  = "gcats0_malloc_err"

fun gcats0_malloc {n:nat}
  (n: int n): [l:addr] (bytes_v (n, l) | ptr l) = "gcats0_malloc"

fun gcats0_calloc {a:viewtype} {n:nat}
  (n: int n, sz: sizeof_t a): [l:addr] (@[a?][n] @ l | ptr l)

fun gcats0_free {n:nat} {l:addr}
  (pf: bytes_v (n, l) | p: ptr l): void = "gcats0_free"

dataview realloc_v (int, addr, int, addr) =
  | {n,n0:nat} {l0:addr}
      realloc_fail (n0, l0, n, null) of bytes_v (n0, l0)
  | {n,n0:nat} {l0,l:addr | l > null}
      realloc_succ (n0, l0, n, l) of bytes_v (n, l)

fun gcats0_realloc_err {n0,n:nat} {l0:addr}
  (pf: bytes_v (n0, l0) | p: ptr l0, n: int n)
  : [l:addr] (realloc_v (n0, l0, n, l) | ptr l)
  = "gcats0_realloc_err"

fun gcats0_realloc {n0,n:nat} {l0:addr}
  (pf: bytes_v (n0, l0) | p: ptr l0, n: int n)
  : [l:addr] (bytes_v (n, l) | ptr l)
  = "gcats0_realloc"

(* ****** ****** *)

fun gcats1_malloc {sz:nat} (sz: int sz): freeitm = "gcats1_malloc"
fun gcats1_calloc {n,sz:nat} (n: int n, sz: int sz): freeitm
  = "gcats1_calloc"
fun gcats1_free (itm: freeitm): void = "gcats1_free"

(* ****** ****** *)

// bit-tweaking for efficiency

fun pow2_ceil (n: Nat):<> uInt = "pow2_ceil"

fun log2_floor (n: uInt):<> Nat = "log2_floor"
fun log2_ceil (n: uInt):<> Nat = "log2_ceil"

fun div_ceil (n: uInt, d: Pos): Nat = "div_ceil"
fun mod_pow2 (m: uInt, n: Nat): Nat = "mod_pow2"

(* ****** ****** *)

// blocklst0 is doubly-linked

absviewt@ype
block0 = $extype "block0"

absviewt@ype
blocklst0 (ptr: addr, front: int, back: int) = $extype "blocklst0"

//

dataview block0_malloc_v (int, addr) =
  | {n:nat} block0_malloc_fail (n, null)
  | {n:nat} {l:addr | l > null}
      block0_malloc_succ (n, l) of (block0 @ l, bytes_v (n, l+sizeof(block0)))

fun block0_malloc_err {n:nat}
  (n: int n): [l:addr] (block0_malloc_v (n, l) | ptr l)
  = "block0_malloc_err"

fun block0_free {n:nat} {l:addr}
  (pf1: block0 @ l, pf2: bytes_v (n, l+sizeof(block0)) | p: ptr l): void
  = "block0_free"

//

fun blocklst0_is_beg {f,b:nat} {l0,l:addr}
  (pf: !blocklst0 (l, f, b) @ l0 | p: ptr l): bool(f==0) = "blocklst0_is_beg"

fun blocklst0_is_end {f,b:nat} {l0,l:addr}
  (pf: !blocklst0 (l, f, b) @ l0 | p: ptr l): bool(b==0) = "blocklst0_is_end"

//

fun blocklst0_next {f,b:nat | b > 0}  {l0,l:addr}
  (pf: blocklst0 (l, f, b) @ l0 | p: ptr l)
  : [l:addr] (blocklst0 (l, f+1, b-1) @ l0 | ptr l)
  = "blocklst0_next"

fun blocklst0_prev {f,b:nat | f > 0}  {l0,l:addr}
  (pf: blocklst0 (l, f, b) @ l0 | p: ptr l)
  : [l:addr] (blocklst0 (l, f-1, b+1) @ l0 | ptr l)
  = "blocklst0_next"

//

fun blocklst0_remove {f,b:nat | f+b > 0} {l0,l:addr}
  (pf: blocklst0 (l, f, b) @ l0 | p0: ptr l0, p: ptr l)
  : [l1:addr] (blocklst0 (l1, 0, f+b-1) @ l0, block0 @ l | ptr l)
  = "blocklst0_remove"

//

sta the_blocklst0_addr : addr

fun the_blocklst0_get ()
  : [n:nat] [l1:addr] (blocklst0 (l1, 0, n) @ the_blocklst0_addr | void)
  = "the_blocklst0_get"

fun the_blocklst0_set {n:nat} {l:addr}
  (pf: blocklst0 (l, 0, n) @ the_blocklst0_addr | (*none*)): void
  = "the_blocklst0_set"

fun the_blocklst0_cons {l:addr}
  (pf: block0 @ l | x: ptr l): void
  = "the_blocklst0_cons"

// This is an unsafe function:
dataview blocklst0_take_v (addr, addr) =
  | {l:addr} blocklst0_take_fail (l, null)
  | {l,l0:addr | l0 <> null}
      blocklst0_take_succ (l0+sizeof(block0), l0) of block0 @ l0

fun the_blocklst0_take_err {l:addr}
  (p: ptr l): [l0:addr] (blocklst0_take_v (l, l0) | ptr l0)
  = "the_blocklst0_take_err"

fun the_blocklst0_realloc_err {n0,n:nat} {l0:addr}
  (pf: bytes_v (n0, l0) | p: ptr l0, n: int n)
  : [l:addr] (realloc_v (n0, l0, n, l) | ptr l)
  = "the_blocklst0_realloc_err"

(* ****** ****** *)

(* end of gc.sats *)
