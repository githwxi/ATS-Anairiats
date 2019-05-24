(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
**
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "location.sats"

(* ****** ****** *)

datatype token_node =
  | TOKeof of () // token indicating end-of-file
  | TOKextcode of string
  | TOKident of string
  | TOKkeychar of char
  | TOKkeyword of string
  | TOKpercperc of ()
  | TOKpostamble of string
  | TOKpreamble of string
  | TOKptbrackstr of string

where token = '{
  token_loc= location_t, token_node= token_node
}

typedef tokenlst = List (token)
typedef tokenopt = Option (token)

(* ****** ****** *)

fun token_none_make (): token

(* ****** ****** *)

fun token_eof_make (loc: location_t): token
fun token_extcode_make (loc: location_t, code: string): token
fun token_ident_make (loc: location_t, name: string): token
fun token_keychar_make (loc: location_t, name: char): token
fun token_keyword_make (loc: location_t, name: string): token
fun token_percperc_make (loc: location_t): token
fun token_postamble_make (loc: location_t, code: string): token
fun token_preamble_make (loc: location_t, code: string): token
fun token_ptbrackstr_make (loc: location_t, str: string): token

(* ****** ****** *)

fun fprint_token {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, tok: token): void

fun print_token (tok: token): void
fun prerr_token (tok: token): void

(* ****** ****** *)

(* end of [token.sats] *)
