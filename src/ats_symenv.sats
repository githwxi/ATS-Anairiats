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
// Time: October 2008

(* ****** ****** *)

staload Sym = "ats_symbol.sats"
typedef sym_t = $Sym.symbol_t

(* ****** ****** *)

absviewtype symmap_t (itm: t@ype) // boxed type
typedef symmapref (itm: t@ype) = ref (symmap_t itm)

(* ****** ****** *)

fun symmap_make {itm:t@ype} ():<> symmap_t (itm)
fun{itm:t@ype} symmap_free (map: symmap_t itm):<> void

(* ****** ****** *)

fun{itm:t@ype} symmap_search
  (map: !symmap_t itm, _: sym_t): Option_vt itm
// end of [symmap_search]

fun{itm:t@ype} symmap_ref_search
  (map: symmapref itm, _: sym_t): Option_vt itm
// end of [symmapref_search]

fun{itm:t@ype} symmap_list_get
  (map: !symmap_t itm): List_vt @(sym_t, itm)
// end of [symmap_list_get]

fun{itm:t@ype} symmap_reflist_get
  (map: symmapref itm): List_vt @(sym_t, itm)
// end of [symmap_reflist_get]

(* ****** ****** *)

fun{itm:t@ype} symmap_insert
  (m: !symmap_t (itm), k: sym_t, i: itm):<> void
// end of [symmap_insert]

fun{itm:t@ype} symmap_remove
  (m: !symmap_t (itm), k: sym_t):<> Option_vt itm
// end of [symmap_remove]

(* ****** ****** *)

// list a map in pre-order
fun{itm:t@ype}
  symmap_list_inf (m: !symmap_t itm):<> List_vt @(sym_t, itm)
// end of [fun]

(* ****** ****** *)

abstype
symenv_t (itm: t@ype) // boxed type

(* ****** ****** *)

fun symenv_make {itm:t@ype} (): symenv_t (itm)

(* ****** ****** *)

fun{itm:t@ype}
symenv_insert_fst
  (env: symenv_t itm, k: sym_t, i: itm): void
// end of [symenv_insert_fst]

fun{itm:t@ype}
symenv_remove_fst
  (env: symenv_t itm, k: sym_t): Option_vt itm
// end of [symenv_remove_fst]

(* ****** ****** *)

fun{itm:t@ype}
symenv_search_all
  (env: symenv_t itm, k: sym_t): Option_vt itm
// end of [symenv_search_all]

(* ****** ****** *)

fun{itm:t@ype}
symenv_pervasive_search
  (env: symenv_t itm, k: sym_t): Option_vt itm
// end of [symenv_pervasive_search]

fun{itm:t@ype}
symenv_pervasive_replace
  (env: symenv_t itm, k: sym_t, i: itm): Option_vt itm
// end of [symenv_pervasive_replace]

(* ****** ****** *)

fun{itm:t@ype}
symenv_pop (env: symenv_t itm): void

fun symenv_push {itm:t@ype} (env: symenv_t itm): void

(*
** swap the contents of [env.map] and [r_m]
*)
fun symenv_swap
  {itm:t@ype} (env: symenv_t itm, r_m: symmapref itm): void
// end of [symenv_swap]

(* ****** ****** *)

fun symenv_top_get
  {itm:t@ype} (env: symenv_t itm): symmap_t itm
fun symenv_reftop_get
  {itm:t@ype} (env: symenv_t itm): ref (symmap_t itm)

(* ****** ****** *)

fun{itm:t@ype}
symenv_localjoin (env: symenv_t itm): void

(* ****** ****** *)

fun symenv_save
  {itm:t@ype} (env: symenv_t itm): void
fun{itm:t@ype}
symenv_restore (env: symenv_t itm): void

(* ****** ****** *)

fun symenv_pervasive_add
  {itm:t@ype} (env: symenv_t itm, map: symmap_t itm): void
// end of [symenv_pervasive_add]

(* ****** ****** *)

(* end of [ats_symenv.sats] *)
