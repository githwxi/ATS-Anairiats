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
// Time: November 2007
//
(* ****** ****** *)

staload Sym = "ats_symbol.sats"
typedef name = $Sym.symbol_t

fun the_namespace_add (name: name): void

fun the_namespace_search
  {a:type} (f: !name -<cloptr1> Option_vt a): Option_vt a
// end of [the_namespace_search]

(* ****** ****** *)

fun the_namespace_pop (): void
fun the_namespace_push (): void
fun the_namespace_restore (): void
fun the_namespace_save (): void
fun the_namespace_localjoin (): void

(* ****** ****** *)

fun the_namespace_initialize (): void

(* ****** ****** *)

(* end of [ats_namespace.sats] *)
