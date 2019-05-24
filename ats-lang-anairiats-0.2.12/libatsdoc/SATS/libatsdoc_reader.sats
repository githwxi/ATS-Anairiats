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

%{#
#include "libatsdoc/CATS/libatsdoc_reader.cats"
%} // end of [%{#]

(* ****** ****** *)

absviewt@ype
reader_vt0ype =
  $extype "libatsdoc_reader_struct"
viewtypedef reader = reader_vt0ype

(* ****** ****** *)

fun reader_initialize_filp
  {m:file_mode} {l:addr} (
  pfmod: file_mode_lte (m, r)
, pffil: FILE m @ l
| r: &reader? >> reader, p: ptr l
) : void // end of [reader_initialize_filp]

(* ****** ****** *)

fun reader_initialize_getc (
  r: &reader? >> reader, getc: () -<cloptr1> int
) : void // end of [reader_initialize_getc]

(* ****** ****** *)

fun reader_initialize_string (
  r: &reader? >> reader, inp: string
) : void // end of [reader_initialize_string]

(* ****** ****** *)

fun reader_uninitialize (
  r: &reader >> reader?
) : void // end of [reader_uninitialize]

(* ****** ****** *)

fun reader_get_char (r: &reader): int // HX: EOF(-1) is returned at the end

(* ****** ****** *)

(* end of [libatsdoc_reader.sats] *)
