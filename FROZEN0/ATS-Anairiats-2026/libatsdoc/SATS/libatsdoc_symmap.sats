(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2012 Hongwei Xi, ATS Trustful Software, Inc.
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
// Start Time: July, 2011
//
(* ****** ****** *)

staload
SYM = "libatsdoc/SATS/libatsdoc_symbol.sats"
typedef symbol = $SYM.symbol

(* ****** ****** *)

absviewtype
symmap_vtype (itm:type)
stadef symmap = symmap_vtype

fun symmap_make_nil
  {itm:type} ():<> symmap (itm)

fun symmap_free
  {itm:type} (map: symmap (itm)):<> void

fun
symmap_search
  {itm:type}
  (map: !symmap itm, k: symbol):<> Option_vt itm
// end of [symmap_search]

fun
symmap_insert
  {itm:type} (
  map: &symmap (itm), key: symbol, itm: itm
) :<> void // end of [symmap_insert]

(* ****** ****** *)

(* end of [libatsdoc_symmap.sats] *)
