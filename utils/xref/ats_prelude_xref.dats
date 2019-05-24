(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
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
// Time: March 2009
//
(* ****** ****** *)

//
// This file is solely for generating cross-references to
// static and dynamic constants declared in various files
// in the directory [$ATSHOME/prelude]/
//
// A typical use is like this:
//
// atsopt --xrefprelude --posmark_xref=XREF -d ats_prelude_xref.dats > /dev/null
//
// where [XREF] should be replaced with the name of a directory
// that is already created for storing the files that are to be
// generated for cross-referencing.
//

(* ****** ****** *)
//
staload "prelude/basics_sta.sats"
//
staload "prelude/sortdef.sats"
//
staload "prelude/basics_dyn.sats"
//
staload "prelude/macrodef.sats"
//
staload "prelude/SATS/arith.sats"
staload "prelude/SATS/vsubrw.sats"
//
staload "prelude/SATS/bool.sats"
//
staload "prelude/SATS/byte.sats"
//
staload "prelude/SATS/char.sats"
//
staload "prelude/SATS/extern.sats"
//
staload "prelude/SATS/filebas.sats"
//
staload "prelude/SATS/float.sats"
//
staload "prelude/SATS/integer.sats"
staload "prelude/SATS/integer_fixed.sats"
staload "prelude/SATS/integer_ptr.sats"
//
staload "prelude/SATS/lazy.sats"
staload "prelude/SATS/lazy_vt.sats"
//
staload "prelude/SATS/memory.sats"
//
staload "prelude/SATS/pointer.sats"
//
staload "prelude/SATS/printf.sats"
//
staload "prelude/SATS/reference.sats"
//
staload "prelude/SATS/sizetype.sats"
//
staload "prelude/SATS/string.sats"
//
staload "prelude/SATS/array.sats"
staload "prelude/SATS/array0.sats"
//
staload "prelude/SATS/list.sats"
staload "prelude/SATS/list0.sats"
staload "prelude/SATS/list_vt.sats"
//
staload "prelude/SATS/matrix.sats"
staload "prelude/SATS/matrix0.sats"
//
staload "prelude/SATS/option.sats"
staload "prelude/SATS/option0.sats"
//
staload "prelude/SATS/ptrarr.sats"
//
staload "prelude/SATS/unsafe.sats"

(* ****** ****** *)

(* end of [ats_prelude_xref.dats] *)
