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
// Time: May 2008

(* ****** ****** *)

dataviewtype
charlst_vt (int) =
  | CHARLSTnil (0)
  | {n:nat} CHARLSTcons (n+1) of (char, charlst_vt n)
// end of [charlst_vt]

viewtypedef Charlst_vt = [n:nat] charlst_vt (n)

fun charlst_free {n:nat} (cs: charlst_vt n): void

fun charlst_length {n:nat} (cs: !charlst_vt n): int n

fun charlst_add_string {m,n:nat}
  (cs: charlst_vt m, str: string n): charlst_vt (m+n)

// the returned string represents the reverse of [cs]
fun string_make_charlst_rev {n:nat} (cs: charlst_vt n): string n
fun string_make_charlst_rev_int {n:nat} (cs: charlst_vt n, n: int n): string n
  = "string_make_charlst_rev_int"

(* ****** ****** *)

(* end of [ats_charlst.sats] *)
