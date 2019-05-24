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

abstype hashtbl_t (key:t@ype,item:viewt@ype) // boxed type

(* ****** ****** *)

exception HashTableIsNullException

(* ****** ****** *)

fun hashtbl_make_hint
  {key:t@ype;item:viewt@ype} {sz:pos}
  (hash: key -<fun> uint, eq: (key, key) -<fun> bool, hint: int sz)
  :<> hashtbl_t (key, item)

fun hashtbl_str_make_hint
  {item:viewt@ype} {sz:pos} (hint: int sz):<> hashtbl_t (string, item)

fun{key:t@ype;item:t@ype} hashtbl_clear
  (hashtbl: hashtbl_t (key, item)):<!ref> void

fun{key:t@ype;item:t@ype} hashtbl_search
  (hashtbl: hashtbl_t (key, item), k: key):<!ref> Option_vt item

fun{key:t@ype;item:viewt@ype} hashtbl_insert
  (hashtbl: hashtbl_t (key, item), k: key, i: item):<!ref> Option_vt item

fun{key:t@ype;item:viewt@ype} hashtbl_remove
  (hashtbl: hashtbl_t (key, item), k: key):<!ref> Option_vt (item)

(* ****** ****** *)

(* end of [ats_hashtbl.sats] *)
