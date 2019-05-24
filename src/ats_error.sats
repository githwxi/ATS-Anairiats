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
// Time: July 2007
//
(* ****** ****** *)

(* ats_error: some common error reporting functions *)

(* ****** ****** *)

(*
staload "ats_location.sats"
*)

(* ****** ****** *)

(*
fun error {a:viewt@ype} (msg: string): a
fun error_location {a:viewt@ype} (loc: location_t, msg: string): a
*)

(* ****** ****** *)

exception FatalErrorException
fun abort {a:viewt@ype} ():<!exn> a // raising FatalErrorException

exception DeadCodeException
// if this function is ever called at run-time, something is wrong!
fun deadcode {a:viewt@ype} (msg: string): a

(* ****** ****** *)

(* end of [ats_error.sats] *)
