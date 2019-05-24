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
// March 2008
//
(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_stadyncst2.sats"

(* ****** ****** *)

staload "ats_string_parse.sats"

(* ****** ****** *)

implement
s2exp_make_printf_c_argtype (fat) = begin
  case+ fat of
  | FAT_c_char () => s2exp_char_t0ype ()
  | FAT_c_double () => s2exp_double_t0ype ()
  | FAT_c_double_long () => s2exp_double_long_t0ype ()
  | FAT_c_int () => s2exp_int_t0ype ()
  | FAT_c_int_long () => s2exp_lint_t0ype ()
  | FAT_c_int_long_long () => s2exp_llint_t0ype ()
  | FAT_c_int_short () => s2exp_sint_t0ype ()
  | FAT_c_int_short_short () => s2exp_ssint_t0ype ()
  | FAT_c_ptr () => s2exp_ptr_type ()
  | FAT_c_string () => s2exp_string_type ()
  | FAT_c_uint () => s2exp_uint_t0ype ()
  | FAT_c_uint_long () => s2exp_ulint_t0ype ()
  | FAT_c_uint_long_long () => s2exp_ullint_t0ype ()
  | FAT_c_uint_short () => s2exp_usint_t0ype ()
  | FAT_c_uint_short_short () => s2exp_ussint_t0ype ()
end // end of [s2exp_make_printf_c_argtype]

implement
s2exp_make_printf_c_argtypes (fats) = let
  fun aux (fats: printf_c_argtypes): s2explst = begin
    case+ fats of
    | ~list_vt_cons (fat, fats) => begin
        list_cons (s2exp_make_printf_c_argtype fat, aux fats)
      end // end of [list_vt_cons]
    | ~list_vt_nil () => list_nil () // end of [list_vt_nil]
  end // end of [aux]
in
  s2exp_tylst (aux fats)
end // end of [s2exp_make_printf_c_argtypes]

(* ****** ****** *)

(* end of [ats_string_parser.dats] *)
