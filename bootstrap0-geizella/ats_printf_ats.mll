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
(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

{
  open Ats_misc
  module P = Printf

  exception Illegal_printf_ats_string

  (* Keep these values in sync with the runtime system *)
  let flag_grouping = (1 lsl 0)
  let flag_left_justify = (1 lsl 1)
  let flag_use_sign = (1 lsl 2)
  let flag_prefix_space = (1 lsl 3)
  let flag_alt_form = (1 lsl 4)
  let flag_zero_padding = (1 lsl 5)

  let the_legal_spec_list: char list = [
    'a'; 'A'; 'c'; 'd'; 'e'; 'E'; 'f'; 'F'; 'g';
    'G'; 'i'; 'o'; 'p'; 's'; 'u'; 'x'; 'X'; 'y'
  ]

(*
  type length_spec =
    | LS_none | LS_h | LS_hh | LS_j | LS_l | LS_ll | LS_L | LS_t | LS_z
*)

  let __LS_none = 0
  and __LS_h = 1
  and __LS_hh = 2
  and __LS_j = 3
  and __LS_l = 4
  and __LS_ll = 5
  and __LS_L = 6
  and __LS_t = 7
  and __LS_z = 8

(*
  type type_spec =
    | TS_a | TS_A | TS_c | TS_C | TS_d | TS_e | TS_E | TS_f | TS_F | TS_g
    | TS_G | TS_i | TS_o | TS_p | TS_s | TS_S | TS_u | TS_x | TS_X | TS_y

  let translate_spec_to_code = function
    | 'a' -> TS_a
    | 'A' -> TS_A
    | 'c' -> TS_c
    | 'd' -> TS_d
    | 'e' -> TS_e
    | 'E' -> TS_E
    | 'f' -> TS_f
    | 'F' -> TS_F
    | 'g' -> TS_g
    | 'G' -> TS_G
    | 'i' -> TS_i
    | 'o' -> TS_o
    | 'p' -> TS_p
    | 'u' -> TS_u
    | 'x' -> TS_x
    | 'X' -> TS_X
    | 's' -> TS_s
    | 'y' -> TS_y
    | _ -> raise Illegal_printf_ats_string
*)

  let translate_spec_to_type (spec: char) (ls: int): string =
    match spec with
      | 'a' -> "FMT_double"
      | 'A' -> "FMT_double"
      | 'c' -> "FMT_char"
      | 'd' when ls == __LS_h -> "FMT_sint"
      | 'd' when ls == __LS_l -> "FMT_lint"
      | 'd' when ls == __LS_ll -> "FMT_llint"
      | 'd' -> "FMT_int"
      | 'e' -> "FMT_double"
      | 'E' -> "FMT_double"
      | 'f' -> "FMT_double"
      | 'F' -> "FMT_double"
      | 'g' -> "FMT_double"
      | 'G' -> "FMT_double"
      | 'i' -> "FMT_int"
      | 'o' -> "FMT_uint"
      | 'p' -> "FMT_ptr"
      | 's' -> "FMT_string"
      | 'u' -> "FMT_uint"
      | 'x'-> "FMT_uint"
      | 'X' -> "FMT_uint"
      | 'y' -> "FMT_apply"
      | _ -> raise Illegal_printf_ats_string

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
      | _ -> raise Illegal_printf_ats_string

  let translate_flags flag_list =
    let aux sofar cur = match cur with
      | '\'' -> (sofar lor flag_grouping)
      | '-' -> (sofar lor flag_left_justify)
      | '+' -> (sofar lor flag_use_sign)
      | ' ' -> (sofar lor flag_prefix_space)
      | '#' -> (sofar lor flag_alt_form)
      | '0' -> (sofar lor flag_zero_padding)
      | _ -> raise Illegal_printf_ats_string
    in (List.fold_left aux 0 flag_list)
 
  let translate_prec (prec: string): string =
    match prec with
      | "" -> "-1" | "." -> "0"
      | x -> Char.escaped (String.get x (String.length x - 1))

  let translate_width = function "" -> "~1" | x -> x

  let verify_flags (flags: char list) (spec: char) =
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
	if not (b) then raise Illegal_printf_ats_string in
      List.iter aux flags

  let verify_prec (prec: string) (spec: char): unit =
    match prec with
      | "" -> ()
      | x -> begin
	  if List.mem spec the_legal_spec_list then ()
	  else raise Illegal_printf_ats_string
	end

  let verify_length (length: int) (spec: char) = 
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
      if not (b) then raise Illegal_printf_ats_string

  let build_printf_ats_output
    (flags: string) (width: string) (prec: string)
    (length: string) (spec: char) (rest: string): string = 
    let flags_chars = string_explode flags in
    let () = verify_flags flags_chars spec in
    let flags_int = translate_flags flags_chars in
    let width_str = translate_width width in
    let () = verify_prec prec spec in
    let length_int = translate_length length in
    let () = verify_length length_int spec in
    let prec_str = translate_prec prec in
    let spec_type = translate_spec_to_type spec length_int in
      P.sprintf "$format:%s(%c,%d,%d,%s,%s,%s)"
	spec_type spec length_int flags_int width_str prec_str rest
 
  let build_literal_output str rest =
    P.sprintf "$format:FMT_literal(\"%s\",%s)" str rest
}

let integer = ((['1'-'9']['0'-'9']*) | '0')

rule translate = parse
  | '%' { (flags lexbuf) }
  | ([^ '%'] | "%%")* as str { (build_literal_output str (translate lexbuf)) }
  | eof { "$format:FMT_init ()" }
  | _ { raise Illegal_printf_ats_string }

and flags = parse
  | (''' | '-' | '+' | ' ' | '#' | '0')* as str { (width str lexbuf) }

and width flag_v = parse
  | (integer)? as str { (precision flag_v str lexbuf) }

and precision flag_v width_v = parse
  | ('.' integer?)? as str { (length flag_v width_v str lexbuf) }

and length flag_v width_v prec_v = parse
  | ("h" | "hh" | "j" | "l" | "ll" | "L" | "t" | "z" )? as str
    { (specifier flag_v width_v prec_v str lexbuf) }

and specifier flag_v width_v prec_v length_v = parse
  | ( 'a' | 'A' | 'c' | 'd' | 'e' | 'E' | 'f' | 'F' | 'g' |
      'G' | 'i' | 'o' | 'p' | 's' | 'u' | 'x' | 'X' | 'y' ) as chr
    { (build_printf_ats_output flag_v width_v prec_v length_v chr (translate lexbuf)) }
  | _ { raise Illegal_printf_ats_string }

{
  let printf_ats_string_parse (s: string): string =
    let lexbuf = Lexing.from_string s in translate lexbuf
}

(* ****** ****** *)

(* end of [ats_printf_ats.mll] *)
