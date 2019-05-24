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
#include "contrib/linux/linux/CATS/fcntl.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

macdef O_ACCMODE = $extval (uint, "O_ACCMODE")
macdef O_RDONLY	= $extval (uint, "O_RDONLY")
macdef O_WRONLY	= $extval (uint, "O_WRONLY")
macdef O_RDWR = $extval (uint, "O_RDWR")

macdef O_CREAT = $extval (uint, "O_CREAT")
macdef O_EXCL = $extval (uint, "O_EXCL")
macdef O_NOCTTY = $extval (uint, "O_NOCTTY")
macdef O_TRUNC = $extval (uint, "O_TRUNC")
macdef O_APPEND = $extval (uint, "O_APPEND")
macdef O_NONBLOCK = $extval (uint, "O_NONBLOCK")

macdef O_DSYNC = $extval (uint, "O_DSYNC")
macdef FASYNC = $extval (uint, "FASYNC") // BSD compatibility
macdef O_DIRECT = $extval (uint, "O_DIRECT")

macdef O_LARGEFILE = $extval (uint, "O_LARGEFILE")
macdef O_DIRECTORY = $extval (uint, "O_DIRECTORY")
macdef O_NOFOLLOW = $extval (uint, "O_NOFOLLOW")
macdef O_NOATIME = $extval (uint, "O_NOATIME")
macdef O_CLOEXEC = $extval (uint, "O_CLOEXEC")

(* ****** ****** *)

(* end of [fcntl.sats] *)
