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

staload "types.sats"

(* ****** ****** *)

%{#
#include "contrib/linux/linux/CATS/kdev_t.cats"
%} // end of [%{#]

(* ****** ****** *)

fun MAJOR (dev: dev_t): int = "atsctrb_linux_MAJOR"
fun MINOR (dev: dev_t): int = "atsctrb_linux_MINOR"

fun MKDEV
  (major: int, minor: int): dev_t = "atsctrb_linux_MKDEV"
// end of [MKDEV]
  
(* ****** ****** *)

(* end of [kdev_t.sats] *)
