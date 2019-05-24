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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// March 2008
//
(* ****** ****** *)

sortdef vt0p = viewt@ype

fun{a:vt0p}
array_ptr_alloc
  {n:nat}
(
  asz: int n
) :<> [l:addr | l > null]
  (free_gc_v (a?, n, l), array_v (a?, n, l) | ptr l)
  = "ats_array_ptr_alloc_tsz"

fun
array_ptr_alloc_tsz
  {a:vt0p}{n:nat}
(
  asz: int n, tsz: sizeof_t a
) :<> [l:addr | l > null]
  (free_gc_v (a?, n, l), array_v (a?, n, l) | ptr l)
  = "ats_array_ptr_alloc_tsz"

(* ****** ****** *)

fun array_ptr_free
  {a:vt0p} {n:int} {l:addr}
(
  pfgc: free_gc_v (a?, n, l), pfarr: array_v (a?, n, l) | p: ptr l
) :<> void = "ats_array_ptr_free" 

(* ****** ****** *)

fun{a:t@ype}
array_ptr_initialize_elt{n:nat}
(
  base: &(@[a?][n]) >> @[a][n], asz: int n, x: a
) :<> void // end of [array_ptr_initialize_elt]

fun{a:t@ype}
array_ptr_make_elt
  {n:nat} (
  asz: int n, x:a
) :<> [l:addr | l > null]
  (free_gc_v (a?, n, l), array_v (a, n, l) | ptr l)
// end of [array_ptr_make_elt]

(* ****** ****** *)

fun{a:t@ype}
array_ptr_initialize_lst
  {n:nat}
(
  base: &(@[a?][n]) >> @[a][n], xs: list (a, n)
) :<> void // endfun

fun{a:t@ype}
array_ptr_make_lst
  {n:nat} (
  asz: int n, xs: list (a, n)
) :<> [l:addr | l > null]
(
  free_gc_v (a?, n, l), array_v (a, n, l) | ptr l
) // end of [array_ptr_make_lst]

(* ****** ****** *)
//
// HX: not used
//
fun{a:vt0p}
array_ptr_initialize_lst_vt
  {n:nat} (
  base: &(@[a?][n]) >> @[a][n], xs: list_vt (a, n)
) :<> void // end of [array_ptr_initialize_lst_vt]

fun{a:vt0p}
array_ptr_make_lst_vt
  {n:nat} (
  asz: int n, xs: list_vt (a, n)
) :<> [l:addr | l > null] (
  free_gc_v (a?, n, l), array_v (a, n, l) | ptr l
) // end of [array_ptr_make_lst_vt]

(* ****** ****** *)

(* end of [ats_array.sats] *)
