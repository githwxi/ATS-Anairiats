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
** Copyright (C) 2002-2008 Hongwei Xi, ATS Trustworthy Software, Inc.
**
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

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)
//
// HX: for initializing [libatsdoc]
//
(* ****** ****** *)

dynload "libatsdoc/DATS/libatsdoc_error.dats"
dynload "libatsdoc/DATS/libatsdoc_filename.dats"
dynload "libatsdoc/DATS/libatsdoc_location.dats"
dynload "libatsdoc/DATS/libatsdoc_reader.dats"
dynload "libatsdoc/DATS/libatsdoc_lexbuf.dats"
dynload "libatsdoc/DATS/libatsdoc_symbol.dats"
dynload "libatsdoc/DATS/libatsdoc_symmap.dats"
dynload "libatsdoc/DATS/libatsdoc_atext.dats"

(* ****** ****** *)

(* end of [dynloadall.dats] *)
