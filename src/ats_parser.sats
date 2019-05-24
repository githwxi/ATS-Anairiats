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
// Start Time: August 2007
//
(* ****** ****** *)

staload Lex = "ats_lexer.sats"
typedef token_t = $Lex.token_t
staload Fil = "ats_filename.sats"
typedef fil_t = $Fil.filename_t

(* ****** ****** *)
//
// HX: for indicating which kind of syntactic entity is to be parsed
//
datatype yybeg =
  | YYBEGnone of ()
//
  | YYBEGi0de of ()
  | YYBEGs0rtid of ()
  | YYBEGsi0de of ()
  | YYBEGdi0de of ()
//
  | YYBEGs0exp of ()
  | YYBEGd0exp of ()
//
  | YYBEGd0ecseq_sta of ()
  | YYBEGd0ecseq_dyn of ()
// end of [yybeg]

(* ****** ****** *)

fun token_of_yybeg (tok: yybeg): token_t

(* ****** ****** *)

local

staload "ats_syntax.sats"

in // in of [local]

datatype yyres =
  | YYRESi0de of i0de
//
  | YYRESs0exp of s0exp
  | YYRESd0exp of d0exp
//
  | YYRESd0eclst of d0eclst
// end of [yyres]

typedef d0eclst = d0eclst

end // end of [local]

(* ****** ****** *)

fun parse_from_stdin_yyres (tok: yybeg): yyres
fun parse_from_stdin_d0eclst (flag: int): d0eclst

(* ****** ****** *)

fun parse_from_filename_yyres (tok: yybeg, fil: fil_t): yyres
fun parse_from_filename_d0eclst (flag: int, fil: fil_t): d0eclst

(* ****** ****** *)

(* end of [ats_parser.sats] *)
