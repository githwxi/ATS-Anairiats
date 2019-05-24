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
#include "contrib/linux/linux/CATS/types.cats"
%} // end of [%{#]

(* ****** ****** *)

abst@ype fd_set = $extype "fd_set"
abst@ype dev_t = $extype "dev_t"
abst@ype ino_t = $extype "ino_t"
abst@ype mode_t = $extype "mode_t"
abst@ype nlink_t = $extype "nlink_t"
abst@ype off_t = $extype "off_t"
abst@ype pid_t = $extype "pid_t"
abst@ype daddr_t = $extype "daddr_t"
abst@ype key_t = $extype "key_t"
abst@ype suseconds_t = $extype "suseconds_t"
abst@ype timer_t = $extype "timer_t"
abst@ype clockid_t = $extype "clockid_t"
abst@ype mqd_t = $extype "mqd_t"

(* ****** ****** *)

abst@ype uid16_t = $extype "uid16_t"
abst@ype uid_t = $extype "uid_t" // uid32_t
abst@ype gid16_t = $extype "gid16_t"
abst@ype gid_t = $extype "gid_t" // gid32_t

(* ****** ****** *)

abst@ype uintptr_t = $extype "uintptr_t"

(* ****** ****** *)

abst@ype fmode_t = $extype "fmode_t"

abst@ype loff_t = $extype "loff_t"

abst@ype time_t = $extype "time_t"

abst@ype clock_t = $extype "clock_t"

abst@ype caddr_t = $extype "caddr_t"

(* ****** ****** *)

abst@ype uint8 = $extype "uint8_t"
abst@ype uint16 = $extype "uint16_t"
abst@ype uint32 = $extype "uint32_t"
abst@ype uint64 = $extype "uint64_t"

(* ****** ****** *)

(* end of [types.sats] *)
