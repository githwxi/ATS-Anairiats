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

(*
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2011
**
*)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

fun strptrlst_free (xs: List_vt (strptr0)): void

(* ****** ****** *)
//
// HX: if [i] is negative, then [strptr_null] is returned.
//
fun strptr_make_segment {n:nat}
  {i,j:int | i <= j; j <= n} (str: string n, i: int i, j: int j): strptr0
// end of [strptr_make_substring]

(* ****** ****** *)

fun fprint_segment {n:nat}
  {i,j:int | 0 <= i; i <= j; j <= n} (
  out: FILEref, str: string n, i: int i, j: int j
) : void // end of [fprint_segment]

(* ****** ****** *)

fun string_split_string_list
  (str: string, pat: string): List_vt (strptr1)
// end of [string_split_string_list]

(* ****** ****** *)

fun string_replace_substring
  {n:nat} {i,ln:nat | i + ln <= n} {k:nat} (
  src: string n, n: int n, i: int i, ln: int ln
, sub: string k, k: int k
) : strptr1 = "atsctrb_string_replace_substring"

(* ****** ****** *)

abstype STRHASHMAPref (itm: t@ype) = ptr

fun strhashmap_make {itm:t@ype} (): STRHASHMAPref (itm)

fun{itm:t@ype}
strhashmap_search
  (tbl: STRHASHMAPref (itm), k0: string): Option_vt (itm)
// end of [strhashmap_search]

fun{itm:t@ype}
strhashmap_insert
  (tbl: STRHASHMAPref (itm), k: string, i: itm):<> void
// end of [hashtbl_insert]

fun{itm:t@ype}
strhashmap_remove
  (tbl: STRHASHMAPref (itm), k0: string): Option_vt (itm)
// end of [strhashmap_remove]

fun{itm:t@ype}
strhashmap_foreach_vclo {v:view} (
  pf: !v
| tbl: STRHASHMAPref (itm), f: &(!v | string, &itm) -<clo> void
) :<> void // end of [strhashmap_foreach_vclo]

fun{itm:t@ype}
strhashmap_listize (tbl: STRHASHMAPref itm): List_vt @(string, itm)

(* ****** ****** *)
//
// HX-2011-08-26: turning file content into a string
//
fun fstringize (fil: FILEref): strptr1 // HX: no error indication

(* ****** ****** *)
//
// HX-2011-08-26:
// replace each occurrence of [pat] with [str] in the input
// taken from [inp] and output the result to [out] // 0/1 for errs
//
fun fsubst_pat_string
  (inp: FILEref, out: FILEref, pat: string, sub: string): int(*err*)
// end of [fsubst_pat_str]

(* ****** ****** *)

(* end of [scripting.sats] *)
