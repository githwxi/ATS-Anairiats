(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
// Start Time: July 2007
//
(* ****** ****** *)

staload "ats_fixity.sats"

(* ****** ****** *)

assume prec_t: t@ype = int

(* ****** ****** *)

#define PRECMIN ~1000000 // this is low enough
#define PRECMAX  1000000 // this is high enough

implement neginf_prec = PRECMIN
implement posinf_prec = PRECMAX

(* ****** ****** *)

implement app_prec = 70

(* ****** ****** *)

implement select_prec = 80 (* .label is a postfix operator *)

(* ****** ****** *)

implement backslash_prec = app_prec + 1
implement infixtemp_prec = 0 (* for temporary infix status *)

(* ****** ****** *)

implement exi_prec_sta = 0
implement uni_prec_sta = 0

(* ****** ****** *)

implement delay_prec_dyn = 0 (* for $delay and $ldelay *)

(* ****** ****** *)

implement exist_prec_dyn = 0 (* for dynamic patterns *)

(* ****** ****** *)

implement dynload_prec_dyn = app_prec + 1

(* ****** ****** *)
//
// HX: supporting [&p->lab] = &(p->lab)
//
implement ptrof_prec_dyn = select_prec - 1

(* ****** ****** *)
//
// HX: supporting [fold@ !p], [free@ !p] and [view@ !p]
//
implement foldat_prec_dyn = app_prec - 1
implement freeat_prec_dyn = app_prec - 1
implement viewat_prec_dyn = app_prec - 1

(* ****** ****** *)

(*
** HX: [invar_prec_sta] must be greater than [trans_prec_sta]
*)
implement invar_prec_sta = 1

(* ****** ****** *)

implement qmark_prec_sta = app_prec - 1

implement qmarkbang_prec_sta = app_prec - 1

implement r0ead_prec_sta = 100 (* highest *)

implement trans_prec_sta = 0 (* lowest *)

implement crypt_prec_dyn = 0 (* lowest *)

implement deref_prec_dyn = 100 (* highest *)

(* ****** ****** *)

implement int_of_prec (p) = p

implement prec_make_int (i) = case+ 0 of
  | _ when i <= PRECMIN => PRECMIN | _ when i >= PRECMAX => PRECMAX | _ => i
// end of [prec_make_int]

(* ****** ****** *)

implement precedence_inc (p, i) = prec_make_int (p + i)
implement precedence_dec (p, i) = prec_make_int (p - i)

(* ****** ****** *)

implement compare_prec_prec (p1, p2) = compare_int_int (p1, p2)

(* ****** ****** *)

(* end of [ats_fixity_prec.dats] *)
