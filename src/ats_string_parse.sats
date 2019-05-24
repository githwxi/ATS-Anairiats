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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// March 2008

(* ****** ****** *)

staload "ats_staexp2.sats"

(* ****** ****** *)

datatype printf_c_argtype =
  | FAT_c_char
  | FAT_c_double
  | FAT_c_double_long
  | FAT_c_int
  | FAT_c_int_long
  | FAT_c_int_long_long
  | FAT_c_int_short
  | FAT_c_int_short_short
  | FAT_c_ptr
  | FAT_c_string
  | FAT_c_uint
  | FAT_c_uint_long
  | FAT_c_uint_long_long
  | FAT_c_uint_short
  | FAT_c_uint_short_short
// end of [printf_c_argtype]

viewtypedef printf_c_argtypes = List_vt printf_c_argtype

fun printf_c_string_parse (fmt: string): Option_vt (printf_c_argtypes)

fun s2exp_make_printf_c_argtype (_: printf_c_argtype): s2exp
fun s2exp_make_printf_c_argtypes (_: printf_c_argtypes): s2exp

(* ****** ****** *)

(* end of [ats_string_parser.sats] *)
