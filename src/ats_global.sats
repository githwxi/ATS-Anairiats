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
// Time: July 2007

(* ****** ****** *)

(* ats_global: handling some global variables *)

(* ****** ****** *)

fun atsopt_namespace_get
  (): Stropt = "atsopt_namespace_get"
// end of ...

fun atsopt_namespace_set
  (prfx: Stropt): void = "atsopt_namespace_set"
// end of ...

(* ****** ****** *)

fun atsopt_dynloadflag_get
  (): int = "atsopt_dynloadflag_get"
fun atsopt_dynloadflag_set
  (flag: int): void = "atsopt_dynloadflag_set"

(* ****** ****** *)

fun atsopt_dynloadfun_name_get
  (): Stropt = "atsopt_dynloadfun_name_get"
fun atsopt_dynloadfun_name_set
  (name: Stropt): void = "atsopt_dynloadfun_name_set"

(* ****** ****** *)

fun the_IATSdirlst_get (): List(string)
fun the_IATSdirlst_push (dir: string): void

(* ****** ****** *)

(* end of [ats_global.sats] *)
