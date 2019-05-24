(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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

%{#
#include "contrib/linux/linux/CATS/semaphore.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

viewtypedef
semaphore_struct (v: view) =
$extype_struct "semaphore_struct" of {
  __rest= undefined_vt
} // end of [semaphore_struct]
stadef semaphore = semaphore_struct

(* ****** ****** *)

fun up {v:view} (
  pf: v | sem: &semaphore (v)
) : void = "mac#atsctrb_linux_up"

fun down_interruptible
  {v:view} (
  sem: &semaphore (v)
) : [i:int | i <= 0] (
  option_v (v, i==0) | int i
) = "mac#atsctrb_linux_down_interruptible"
// end of [down_interruptible]

(* ****** ****** *)

(* end of [semaphore.sats] *)
