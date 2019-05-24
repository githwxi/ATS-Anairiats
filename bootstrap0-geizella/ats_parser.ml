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

module Err = Ats_error
module Loc = Ats_location
module Fil = Ats_filename
module Syn = Ats_syntax

module Lex = Ats_lexer
module Gra = Ats_grammar

open Ats_misc

(* ****** ****** *)

let parse_with
  (prompt: out_channel -> unit)
  (parsefun: (Lexing.lexbuf -> Gra.token) -> Lexing.lexbuf -> 'ast)
  (lb: Lexing.lexbuf): 'ast =
  try parsefun Lex.token lb
  with
    | Lex.Lexer_error msg -> begin
	prompt stderr;
	prerr_string msg;
	Err.abort ()
      end
    | Parsing.Parse_error -> begin
        prompt stderr;
        Printf.fprintf stderr
          "Parsing error: Char: %a -- %a\n"
          Loc.fprint_position (Loc.position_of (Lexing.lexeme_start_p lb))
          Loc.fprint_position (Loc.position_of (Lexing.lexeme_end_p lb));
	Err.abort ()
      end
(* end of [parse_with] *)

let parse_dec_from_channel
  (is_static: bool) (prompt: out_channel -> unit) (ic: in_channel)
  : Ats_syntax.dec list =
   let () = Lex.initialize () in
   let lb = Lexing.from_channel ic in
    if is_static then parse_with prompt Gra.sdecseqeof lb
    else parse_with prompt Gra.ddecseqeof lb
(* end of [parse_dexp_from_channel] *)

let parse_dec_from_file
  (is_static: bool) (fname: string): Ats_syntax.dec list =
  let prompt: out_channel -> unit =
    function out -> (fprint_string out fname; fprint_string out ": ") in
  let ic = open_in fname in
    parse_dec_from_channel is_static prompt ic
(* end of [parse_dec_from_file] *)

let parse_dexp_from_string (prompt: out_channel -> unit) (s: string)
  : Ats_syntax.dexp =
  let () = Lex.initialize () in
   let lb = Lexing.from_string s in
     parse_with prompt Gra.dexpeof lb
(* end of [parse_dexp_from_string] *)

(* ****** ****** *)

(* end of [ats_parser.ml] *)
