(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

(* ats_fixity: for handing prefix, infix and postfix operators *)

(* ****** ****** *)

type prec
type assoc = L | R | N

type fixity =
  | Nonfix
  | Infix of prec * assoc
  | Prefix of prec
  | Postfix of prec

val prec_of_int : int -> prec

val select_prec : prec
val static_amper_fixity : fixity
val static_amperbang_fixity : fixity
val static_bang_fixity : fixity
val static_qmark_fixity : fixity
val static_trans_fixity : fixity

val dynamic_bang_fixity : fixity

type 'a oper = 
  | Prefixop of prec * ('a -> 'a item)
  | Infixop of prec * assoc * ('a -> 'a -> 'a item)
  | Postfixop of prec * ('a -> 'a item)
	
and 'a item = Atm of 'a | Opr of 'a oper

val associativity : 'a oper -> assoc
val precedence : 'a oper -> prec

val app_item : ('a -> 'a -> 'a item) -> 'a item

val make_backslash_opr : ('a -> Ats_location.location) ->
  (Ats_location.location -> 'a -> 'a list -> 'a) -> 'a item

val make_opr : ('a -> Ats_location.location) ->
  (Ats_location.location -> 'a -> 'a list -> 'a) -> 'a -> fixity -> 'a item

val resolve : Ats_location.location -> 'a item -> ('a item) list -> 'a

(* ****** ****** *)

(* end of [ats_fixity.mli] *)
