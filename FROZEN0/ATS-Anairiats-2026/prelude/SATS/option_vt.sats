(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [option_vt.sats] starts!\n"
#endif

(* ****** ****** *)

sortdef t0p = t@ype and vt0p = viewt@ype

(* ****** ****** *)

fun{a:vt0p}
option_vt_some (x: a): option_vt (a, true)
fun{a:vt0p}
option_vt_none ((*void*)): option_vt (a, false)

(* ****** ****** *)

fun{a:vt0p}
option_vt_make_opt
  {b:bool} (
  b: bool b, x: &opt (a, b) >> a?
) : option_vt (a, b) // end of [option_vt_make_opt]

(* ****** ****** *)

fun option_vt_is_none
  {a:vt0p} {b:bool} (x: !option_vt (a, b)): bool (~b)
fun option_vt_is_some
  {a:vt0p} {b:bool} (x: !option_vt (a, b)): bool ( b)

(* ****** ****** *)

fun{a:vt0p}
option_vt_unsome (opt: option_vt (a, true)):<> a
fun{a:vt0p}
option_vt_unnone (opt: option_vt (a, false)):<> void

(* ****** ****** *)

fun{a:t0p}
option_vt_free (opt: Option_vt (a)): void

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [option_vt.sats] finishes!\n"
#endif

(* end of [option_vt.sats] *)
