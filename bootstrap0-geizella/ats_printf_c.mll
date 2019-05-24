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

(* Author: Rick Lavoie (coldfury AT cs DOT bu DOT edu) *)
(* Author: Hongwei Xi ( hwxi AT cs DOT bu DOT edu ) *)

(* ****** ****** *)

{
  open Printf

  exception Illegal_printf_c_string

  (* Keep these values in sync with the runtime system *)

  let the_legal_prec_list: char list = [
    'a'; 'A'; 'd'; 'e'; 'E'; 'f'; 'F'; 'g'; 'G'; 'i'; 'o'; 's'; 'u'; 'x'; 'X';
  ]

  type printf_c_argtype =
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

  let string_explode s =
    let rec aux res k =
      if k >= 0 then aux (s.[k] :: res) (k-1) else res
    in aux [] (String.length s - 1)

  let __LS_none = 0 and __LS_h = 1 and __LS_hh = 2
  and __LS_j = 3 and __LS_l = 4 and __LS_ll = 5
  and __LS_L = 6 and __LS_t = 7 and __LS_z = 8

  let translate_spec_to_type (spec: char) (ls: int): printf_c_argtype =
    match spec with
      | 'a' -> FAT_c_double
      | 'A' -> FAT_c_double
      | 'c' -> FAT_c_char
      | ('d' | 'i') ->
	  if ls == __LS_h then FAT_c_int_short
	  else if ls == __LS_hh then FAT_c_int_short_short
	  else if ls == __LS_l then FAT_c_int_long
	  else if ls == __LS_ll then FAT_c_int_long_long
	  else FAT_c_int
      | ('e' | 'E' | 'f' | 'F' | 'g' | 'G') ->
	  if ls = __LS_L then FAT_c_double_long else FAT_c_double
      | ('o' | 'u' | 'x' | 'X') ->
	  if ls == __LS_h then FAT_c_uint_short
	  else if ls == __LS_hh then FAT_c_uint_short_short
	  else if ls == __LS_l then FAT_c_uint_long
	  else if ls == __LS_ll then FAT_c_uint_long_long
	  else FAT_c_uint
      | 'p' -> FAT_c_ptr
      | 's' -> FAT_c_string
      | _ -> raise Illegal_printf_c_string

  let verify_flags (spec: char) (flags: char list) =
    let group_ok_list = ['d'; 'f'; 'F'; 'g'; 'G'; 'i'; 'u'] in
    let alter_ok_list = ['a'; 'A'; 'f'; 'F'; 'e'; 'E'; 'g'; 'G'; 'x'; 'X'] in
    let zero_ok_list =
      ['a'; 'A'; 'd'; 'e'; 'E'; 'f'; 'F'; 'g'; 'G'; 'i'; 'o'; 'u'; 'x'; 'X'] in
    let aux (c: char) =
      let b = match c with
	| ('+' | '-' | ' ') -> true
	| '\'' -> List.mem spec group_ok_list
	| '#' -> List.mem spec alter_ok_list
	| '0' -> List.mem spec zero_ok_list
	| _ -> false in
	if not (b) then raise Illegal_printf_c_string in
      List.iter aux flags

  let verify_prec (spec: char) (prec: string): unit =
    match prec with
      | "" -> ()
      | x -> begin
	  if List.mem spec the_legal_prec_list then ()
	  else raise Illegal_printf_c_string
	end

  let translate_length (length: string): int =
    match length with
      | "" -> __LS_none
      | "h" -> __LS_h
      | "hh" -> __LS_hh
      | "j" -> __LS_j
      | "l" -> __LS_l
      | "ll" -> __LS_ll
      | "L" -> __LS_L
      | "t" -> __LS_t
      | "z" -> __LS_z
      | _ -> raise Illegal_printf_c_string

  let verify_length (spec: char) (length: int): unit = 
    let ok_list1 = ['d'; 'i'; 'o'; 'u'; 'x'; 'X'] in
    let ok_list2 =
      [ 'a'; 'A'; 'c'; 'd'; 'e'; 'E'; 'f'; 'F';
	'g'; 'G'; 'i'; 'o'; 's'; 'u'; 'x'; 'X' ] in
    let ok_list3 = ['a'; 'A'; 'e'; 'E'; 'f'; 'F'; 'g'; 'G'] in
    let b = 
      if (length == __LS_none) then true
      else if (length == __LS_l) then List.mem spec ok_list2
      else if (length == __LS_L) then List.mem spec ok_list3
      else if (length == __LS_h) then List.mem spec ok_list1
      else if (length == __LS_hh) then List.mem spec ok_list1
      else if (length == __LS_j) then List.mem spec ok_list1
      else if (length == __LS_ll) then List.mem spec ok_list1
      else if (length == __LS_t) then List.mem spec ok_list1
      else if (length == __LS_z) then List.mem spec ok_list1
      else false in
      if not (b) then raise Illegal_printf_c_string

  let printf_c_output flags width prec length spec = 
    let flags_chars = string_explode flags in
    let () = verify_flags spec flags_chars in
    let () = verify_prec spec prec in
    let length_int = translate_length length in
    let () = verify_length spec length_int in
      translate_spec_to_type spec length_int
}

let integer = ((['1'-'9']['0'-'9']*) | '0')

rule translate ts = parse
  | '%' { (let t = flags lexbuf in translate (t :: ts) lexbuf) }
  | ([^ '%'] | "%%")* { translate ts lexbuf }
  | eof { ts }
  | _ { raise Illegal_printf_c_string }

and flags = parse
  | (''' | '-' | '+' | ' ' | '#' | '0')* as flags_arg { width flags_arg lexbuf }

and width flags_arg = parse
  | (integer)? as width_arg { precision flags_arg width_arg lexbuf }

and precision flags_arg width_arg = parse
  | ('.' integer?)? as prec_arg { length flags_arg width_arg prec_arg lexbuf }

and length flags_arg width_arg prec_arg = parse
  | ("h" | "hh" | "j" | "l" | "ll" | "L" | "t" | "z")? as length_arg
      { specifier flags_arg width_arg prec_arg length_arg lexbuf }

and specifier flags_arg width_arg prec_arg length_arg = parse
  | ( 'a' | 'A' | 'c' | 'd' | 'e' | 'E' | 'f' | 'F' | 'g' |
      'G' | 'i' | 'o' | 'p' | 's' | 'u' | 'x' | 'X' | 'y' ) as spec_arg
      { (printf_c_output flags_arg width_arg prec_arg length_arg spec_arg) }
  | _ { raise Illegal_printf_c_string }

{
  let printf_c_string_parse (s: string): (printf_c_argtype list) option =
    try let lexbuf = Lexing.from_string s in Some (List.rev (translate [] lexbuf))
    with Illegal_printf_c_string -> None
}

(* ****** ****** *)

(* end of [ats_printf_c.mll] *)
