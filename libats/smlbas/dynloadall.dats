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
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

dynload "libats/smlbas/DATS/array.dats"
dynload "libats/smlbas/DATS/array2.dats"
dynload "libats/smlbas/DATS/bool.dats"
dynload "libats/smlbas/DATS/char.dats"
dynload "libats/smlbas/DATS/date.dats"
dynload "libats/smlbas/DATS/list.dats"
dynload "libats/smlbas/DATS/listPair.dats"
dynload "libats/smlbas/DATS/math.dats"
dynload "libats/smlbas/DATS/real.dats"
dynload "libats/smlbas/DATS/string.dats"
dynload "libats/smlbas/DATS/time.dats"

(* ****** ****** *)

(* end of [dynloadall.dats] *)
