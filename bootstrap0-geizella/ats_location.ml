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

(* ats_location: Handling location information. *)

(* ****** ****** *)

open Ats_misc

module PR = Printf
module Fil = Ats_filename

(* ****** ****** *)

type position = {
  char_number : int;
  line_number : int;
  line_offset : int;
}

let nonpos = { char_number = -1; line_number = -1; line_offset = -1; }

(* ****** ****** *)

let the_comment_start_position : position ref = ref nonpos
let the_comment_rest_start_position : (position option) ref = ref None

(* ****** ****** *)

let position_of
  (p: Lexing.position): position = begin
  match !the_comment_rest_start_position with
    | None -> {
	char_number= p.Lexing.pos_cnum;
	line_number= p.Lexing.pos_lnum;
	line_offset= p.Lexing.pos_cnum - p.Lexing.pos_bol;
      } 
    | Some p0 ->
	if p0.char_number <= p.Lexing.pos_cnum then p0
	else {
	  char_number= p.Lexing.pos_cnum;
	  line_number= p.Lexing.pos_lnum;
	  line_offset= p.Lexing.pos_cnum - p.Lexing.pos_bol;
	}
end (* end of [position_of] *)

let min_position_position
  (p1: position) (p2: position) = begin
  if p1.char_number <= p2.char_number then p1 else p2
end (* end of [min_position_position] *)

let max_position_position
  (p1: position) (p2: position) = begin
  if p1.char_number >= p2.char_number then p1 else p2
end (* end of [max_position_position] *)

let fprint_position (out: out_channel) (p: position): unit = begin
  PR.fprintf out "%d (line=%d, offset=%d)" p.char_number p.line_number p.line_offset
end (* end of [fprint_position] *)

let sprintf_position (p: position): string = begin
  PR.sprintf "%d (line=%d, offset=%d)" p.char_number p.line_number p.line_offset
end (* end of [sprintf_position] *)

(* ****** ****** *)

type location = {
  file: Fil.filename; (* file name *)
  start: position; (* start char position *)
  finish: position; (* end char position *)
}

let combine (l1: location) (l2: location): location = {
  file= l1.file;
  start= min_position_position l1.start l2.start;
  finish= max_position_position l1.finish l2.finish;
} (* end of [combine] *)

let fprint out loc = begin
  Fil.fprint out loc.file;
  fprint_string out ": ";
  fprint_position out loc.start;
  fprint_string out " -- ";
  fprint_position out loc.finish;
end

let nonloc = { file= Fil.nonfile; start= nonpos; finish= nonpos; }

let make fname start finish = {
  file= fname; start= start; finish= finish
}

let prerr loc = fprint stderr loc
let print loc = fprint stdout loc

(* ****** ****** *)

let the_location: (location option) ref = ref None

let get_the_location () = match !the_location with
  | None -> begin
      let start = position_of (Parsing.symbol_start_pos ()) in
      let finish = position_of (Parsing.symbol_end_pos ()) in
	make (Fil.filename_get ()) start finish
    end (* end of [None] *)
  | Some loc -> loc
(* end of [get_the_location] *)

let set_the_location loc = the_location := Some loc

let reset_the_location () = the_location := None

(* ****** ****** *)

let get_the_comment_start_position (): position = begin
  !the_comment_start_position
end (* end of [get_the_comment_start_position] *)

let set_the_comment_start_position (lb: Lexing.lexbuf) = begin
  the_comment_start_position := position_of (Lexing.lexeme_start_p lb)
end (* end of [set_the_comment_start_position] *)

let reset_the_comment_start_position (): unit = begin
  the_comment_start_position := nonpos
end (* end of [reset_the_comment_start_position] *)

(* ****** ****** *)

let get_the_comment_rest_start_position (): position option = begin
  !the_comment_rest_start_position
end (* end of [get_the_comment_rest_start_position] *)

let set_the_comment_rest_start_position (lb: Lexing.lexbuf): unit = begin
  the_comment_rest_start_position := Some (position_of (Lexing.lexeme_start_p lb))
end (* end of [set_the_comment_rest_start_position] *)

let reset_the_comment_rest_start_position (): unit = begin
  the_comment_rest_start_position := None
end (* end of [reset_the_comment_rest_start_position] *)

(* ****** ****** *)

let the_string_start_position : position ref = ref nonpos
let the_string_end_position : position ref = ref nonpos

let get_the_string_start_position (): position = !the_string_start_position

let set_the_string_start_position (lb: Lexing.lexbuf): unit =
  the_string_start_position := position_of (Lexing.lexeme_start_p lb)
let set_the_string_end_position (lb: Lexing.lexbuf): unit =
  the_string_end_position := position_of (Lexing.lexeme_end_p lb)

let reset_the_string_start_position (): unit =
  the_string_start_position := nonpos

let get_the_string_location () = match !the_location with
  | None -> make (Fil.filename_get ())
      !the_string_start_position !the_string_end_position
  | Some loc -> loc
(* end of [get_the_string_location] *)

(* ****** ****** *)

let the_extern_start_position : position ref = ref nonpos
let the_extern_end_position : position ref = ref nonpos

let get_the_extern_start_position (): position = !the_extern_start_position

let set_the_extern_start_position (lb: Lexing.lexbuf): unit =
  the_extern_start_position := position_of (Lexing.lexeme_start_p lb)
let set_the_extern_end_position (lb: Lexing.lexbuf): unit =
  the_extern_end_position := position_of (Lexing.lexeme_end_p lb)

let reset_the_extern_start_position (): unit =
  the_extern_start_position := nonpos

let get_the_extern_location () = match !the_location with
  | None -> make (Fil.filename_get ())
      !the_extern_start_position !the_extern_end_position
  | Some loc -> loc
(* end of [get_the_extern_location] *)

(* ****** ****** *)

(* end of [ats_location.ml] *)
