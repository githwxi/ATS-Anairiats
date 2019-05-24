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
// July 2007

(* ****** ****** *)

abst@ype token_t = $extype "ats_int_type"

(* ****** ****** *)
//
val YYBEG_none : token_t
//
val YYBEG_i0de : token_t
val YYBEG_s0rtid : token_t
val YYBEG_si0de : token_t
val YYBEG_di0de : token_t
//
val YYBEG_s0exp : token_t
val YYBEG_d0exp : token_t
//
val YYBEG_d0ecseq_sta : token_t
val YYBEG_d0ecseq_dyn : token_t
//
(* ****** ****** *)
//
// HX: implemented in [ats_lexer.lats]
//
fun eq_token_token
  (t1: token_t, t2: token_t): bool= "eq_token_token"
overload = with eq_token_token

(* ****** ****** *)
//
// HX: implemented in [ats_lexer.lats]
//
fun MAIN (): token_t = "atsopt_lexer_token_get"

(* ****** ****** *)
//
// HX: implemented in [ats_lexer.lats]
//
fun token_is_valid (t: token_t): bool = "atsopt_token_is_valid"

(* ****** ****** *)

(* end of [ats_lexer.sats] *)
