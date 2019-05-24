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

(* The lexical analyzer for ATS *)

(* the prelude of lexer begins *)

{

open Ats_misc
open Ats_grammar

module BI = Big_int
module KW = Ats_keywords
module Loc = Ats_location

exception Lexer_error of string

(* supporting escaped characters in C++ *)
let char_for_backslash (c: char): char = match c with
  | 'a' -> '\007' (* alert *)
  | 'b' -> '\008' (* backspace *)
  | 'f' -> '\012' (* line feed *)
  | 't' -> '\009' (* horizonal tab *)
  | 'n' -> '\010' (* newline *)
  | 'r' -> '\013' (* carriage return *)
  | 'v' -> '\011' (* vertical tab *)
  | c -> c

let code_of_0 = Char.code '0'
let code_of_A = Char.code 'A'
let code_of_a = Char.code 'a'

let char_for_octal_code (lb: Lexing.lexbuf) (i: int): char =
  let aux i =
    Char.code (Lexing.lexeme_char lb i) - code_of_0 in
  let c = 64 * aux i + 8 * aux (i+1) + aux (i+2) in
    Char.chr (c land 0xff)

let char_for_octal_code_3 (lb: Lexing.lexbuf) (i: int): char =
  let d1 = Char.code (Lexing.lexeme_char lb i) - code_of_0 in
  let d2 = Char.code (Lexing.lexeme_char lb (i+1)) - code_of_0 in
  let d3 = Char.code (Lexing.lexeme_char lb (i+2)) - code_of_0 in
    Char.chr (d1 * 64 + d2 * 8 + d3)

let char_for_octal_code_2 (lb: Lexing.lexbuf) (i: int): char =
  let d1 = Char.code (Lexing.lexeme_char lb i) - code_of_0 in
  let d2 = Char.code (Lexing.lexeme_char lb (i+1)) - code_of_0 in
    Char.chr (d1 * 8 + d2)

let char_for_octal_code_1 (lb: Lexing.lexbuf) (i: int): char =
  let d1 = Char.code (Lexing.lexeme_char lb i) - code_of_0 in
    Char.chr d1

let value_of_digit_hex (c: char): int =
  if is_digit c then Char.code c - code_of_0
  else if is_upper c then Char.code c - code_of_A
  else Char.code c - code_of_a


let char_for_hex_code_2 (lb: Lexing.lexbuf) (i: int): char =
  let d1 = value_of_digit_hex (Lexing.lexeme_char lb i) in
  let d2 = value_of_digit_hex (Lexing.lexeme_char lb (i+1)) in
     Char.chr (d1 * 16 + d2)

let char_for_hex_code_1 (lb: Lexing.lexbuf) (i: int): char =
  let d1 = value_of_digit_hex (Lexing.lexeme_char lb i) in
     Char.chr d1

let process_char_oct_3 (lb: Lexing.lexbuf): token = Lchar (char_for_octal_code_3 lb 1)
let process_char_oct_2 (lb: Lexing.lexbuf): token = Lchar (char_for_octal_code_2 lb 1)
let process_char_oct_1 (lb: Lexing.lexbuf): token = Lchar (char_for_octal_code_1 lb 1)

let process_char_hex_2 (lb: Lexing.lexbuf): token = Lchar (char_for_hex_code_2 lb 2)
let process_char_hex_1 (lb: Lexing.lexbuf): token = Lchar (char_for_hex_code_1 lb 2)

(* ****** ****** *)

let the_char_list: (char list) ref = ref []

let store_char (lb: Lexing.lexbuf): unit =
  let c = Lexing.lexeme_char lb 0 in
    the_char_list := c :: !the_char_list

let store_escaped_char (lb: Lexing.lexbuf): unit =
  let c = char_for_backslash (Lexing.lexeme_char lb 1) in
    the_char_list := c :: !the_char_list

let store_char_oct_3 (lb: Lexing.lexbuf): unit =
  let c = char_for_octal_code_3 lb 1 in
    the_char_list := c :: !the_char_list

let store_char_oct_2 (lb: Lexing.lexbuf): unit =
  let c = char_for_octal_code_2 lb 1 in
    the_char_list := c :: !the_char_list

let store_char_oct_1 (lb: Lexing.lexbuf): unit =
  let c = char_for_octal_code_1 lb 1 in
    the_char_list := c :: !the_char_list

let store_char_hex_2 (lb: Lexing.lexbuf): unit =
  let c = char_for_hex_code_2 lb 2 in
    the_char_list := c :: !the_char_list

let store_char_hex_1 (lb: Lexing.lexbuf): unit =
  let c = char_for_hex_code_1 lb 2 in
    the_char_list := c :: !the_char_list

let get_the_string (): string =
  let cs = !the_char_list in
  let () = the_char_list := [] in
     string_of_char_list (List.rev cs)

(* ****** ****** *)

let the_comment_level : int ref = ref 0

let initialize (): unit = begin
  the_comment_level := 0;
  Loc.reset_the_comment_start_position ();
  Loc.reset_the_comment_rest_start_position ();
  Loc.reset_the_string_start_position ();
  Loc.reset_the_extern_start_position (); (* external code *)
end

(* ****** ****** *)

let process_newline lexbuf: unit =
  let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
    Lexing.pos_bol = pos.Lexing.pos_cnum;
  }

let process_comment_open (): unit = begin
    the_comment_level := 1 + !the_comment_level
  end

let process_comment_close (comment: Lexing.lexbuf -> unit) (lb: Lexing.lexbuf)
  : unit =
  let l = !the_comment_level in
    if l > 0 then (the_comment_level := l - 1; comment lb)

let is_comment (): bool = (!the_comment_level > 0)

let process_char (lb: Lexing.lexbuf): token = Lchar (Lexing.lexeme_char lb 0)

let process_escaped_char (lb: Lexing.lexbuf): token =
  let c = Lexing.lexeme_char lb 1 in Lchar (char_for_backslash c)

(* ****** ****** *)

let process_comment_rest_start lexbuf: unit =
  Loc.set_the_comment_rest_start_position lexbuf

(* ****** ****** *)

(* s: string representing integer; n: the length of the string *)
let process_int (s: string) (n: int): intinf =
  let ((neg, i): bool * int) =
    let sgn = String.get s 0 in
      match sgn with '~' -> (true, 1) | _ -> (false, 0) in
  let ((base, i): int * int) =
    if n > i+1 then
      if (String.get s i == '0') then
	let c = String.get s (i+1) in
          if (c == 'x' ||  c == 'X') then (16, i + 2)
          else (8, i + 1)
      else (10, i)
    else (10, i) in
  let rec aux (i: int) (res: intinf): intinf =
    if i < n then
      let d = value_of_digit_hex (String.get s i) in
        aux (i+1) (BI.add_int_big_int d (BI.mult_int_big_int base res))
    else res in
  let res = aux i intinf_zero in
    if neg then BI.minus_big_int res else res
      
let process_int_literal (lb: Lexing.lexbuf): token =
  let s = Lexing.lexeme lb in
  let n = String.length s in
    Lint (process_int s n)

let process_lint_literal (lb: Lexing.lexbuf): token =
  let s = Lexing.lexeme lb in
  let n = String.length s in
    Llint (process_int s (n-1))

let process_uint_literal (lb: Lexing.lexbuf): token =
  let s = Lexing.lexeme lb in
  let n = String.length s in
    Luint (process_int s (n-1))

let process_float_literal (lb: Lexing.lexbuf): token =
  Lfloat (Lexing.lexeme lb)

(* ****** ****** *)
	
let process_alphanum_identifier (lb: Lexing.lexbuf): token =
  let s = Lexing.lexeme lb in
    match KW.ats_keyword_find s with None -> ALPHANUM s | Some t -> t

let process_array_identifier (lb: Lexing.lexbuf): token =
  let s0 = Lexing.lexeme lb in
  let s1 = String.sub s0 0 (String.length s0 - 1) in
    ARRAYIDENT s1

let process_symbolic_identifier (lb: Lexing.lexbuf): token =
  let s = Lexing.lexeme lb in
    match KW.ats_keyword_find s with None -> SYMBOLIC s | Some t -> t

let process_template_identifier (lb: Lexing.lexbuf): token =
  let s0 = Lexing.lexeme lb in
  let s1 = String.sub s0 0 (String.length s0 - 1) in
    TEMPLATEIDENT s1

(* ****** ****** *)

let process_illegal_token (lb: Lexing.lexbuf): 'a =
  let msg =
    Printf.sprintf "Lexer error: illegal token: <%s> at position %d\n"
      (Lexing.lexeme lb) (Lexing.lexeme_start lb) in
    raise (Lexer_error msg)

let process_illegal_char (lb: Lexing.lexbuf): 'a =
  let msg =
    Printf.sprintf "Lexer error: illegal char <%s> at position %d\n"
      (Lexing.lexeme lb) (Lexing.lexeme_start lb) in
    raise (Lexer_error msg)

let process_unclosed_comment (): 'a =
  let msg =
    Printf.sprintf "Lexer error: unclosed comment starting at position %s\n"
      (Loc.sprintf_position (Loc.get_the_comment_start_position ())) in
    raise (Lexer_error msg)

let process_unclosed_string (): 'a =
  let msg =
    Printf.sprintf "Lexer error: unclosed string starting at position %s\n"
      (Loc.sprintf_position (Loc.get_the_string_start_position ())) in
    raise (Lexer_error msg)

let process_unclosed_extern (): 'a =
  let msg =
    Printf.sprintf
      "Lexer error: unclosed external code starting at position %s\n"
      (Loc.sprintf_position (Loc.get_the_extern_start_position ())) in
    raise (Lexer_error msg)

}

(* the prelude of lexer ends *)

let digit_dec = [ '0'-'9' ]

let digit_oct = [ '0'-'7' ]

let digit_hex = [ '0'-'9' 'a'-'f' 'A'-'F']

(*

let symbolic_all = [
  '%' '&' '+' '-' '.' '/' ':' '=' '@' '~' '`' '^' '|' '*'
  '!' '$' '#' '?'
  '<' '>'
  '\\'
]

*)

let symbolic_1 = [
  '%' '&' '+' '-' '.' '/' ':' '=' '@' '~' '`' '^' '|' '*'
  '!' '$' '#' '?'
]

let symbolic_2 = [
  '%' '&' '+' '-' '.' '/' ':' '=' '@' '~' '`' '^' '|' '*'
  '<' '>'
]

let ident_first = [ 'A'-'Z' 'a'-'z' '_' ]

let ident_rest = [ '0'-'9' 'A'-'Z' 'a'-'z' '_' '\'' ]

let identifier = ident_first ident_rest *

let identifier_lbracket = identifier '['

let identifier_lessthan = identifier '<'

let escaped_char = [
  'n' 't' 'v' 'b' 'r' 'f' 'a' '\\' '?' '\'' '"' '(' '[' '{'
]

let newline = '\n'

let blanks = [ '\r' '\t' ' ' ] +

let xX = ('x' | 'X')
let uint_dec = '0' | ['1'-'9'] digit_dec *
let uint_oct = ['1'-'7'] digit_oct *
let uint_hex = ['1'-'9' 'a'-'f' 'A'-'F'] digit_hex *

let uint = uint_dec
         | '0' uint_oct
         | '0' xX uint_hex

let sign_posnegopt = '~'?
let int_literal = sign_posnegopt uint
let lint_literal = sign_posnegopt uint 'L'
let uint_literal = uint 'U'

let float_literal =
  sign_posnegopt digit_dec+ ('.' digit_dec*)? (['e' 'E'] ['+' '-']? digit_dec+)?

rule token = parse
  | "case+" { CASEPLUS }
  | "case-" { CASEMINUS }
  | "dataprop<" { DATAPROPLT }
  | "datatype<" { DATATYPELT }
  | "dataview<" { DATAVIEWLT }
  | "dataviewtype<" { DATAVIEWTYPELT }
  | "for*" { FORSTAR }
  | "fn*" { FNSTAR }
  | "method*" { METHODSTAR }
  | "prop+" { PROPPLUS }
  | "prop-" { PROPMINUS }
  | "type+" { TYPEPLUS }
  | "type-" { TYPEMINUS }
  | "val+" { VALPLUS }
  | "val-" { VALMINUS }
  | "val!" { VALBANG }
  | "val!+" { VALBANGPLUS }
  | "val!-" { VALBANGMINUS }
  | "var*" { VARSTAR }
  | "view+" { VIEWPLUS }
  | "view-" { VIEWMINUS }
  | "viewtype+" { VIEWTYPEPLUS }
  | "viewtype-" { VIEWTYPEMINUS }
  | "while*" { WHILESTAR }
  | "fold@" { FOLDAT }
  | "free@" { FREEAT }
  | "view@" { VIEWAT }
  | "t@ype" { T0YPE }
  | "t@ype+" { T0YPEPLUS }
  | "t@ype-" { T0YPEMINUS }
  | "viewt@ype" { VIEWT0YPE }
  | "viewt@ype+" { VIEWT0YPEPLUS }
  | "viewt@ype-" { VIEWT0YPEMINUS }
  | "abst@ype" { ABST0YPE }
  | "absviewt@ype" { ABSVIEWT0YPE }
  | "#define" { SHARPDEFINE }
  | "#else" { SHARPELSE }
  | "#elsif" { SHARPELSIF }
  | "#endif" { SHARPENDIF }
  | "#error" { SHARPERROR }
  | "#if" { SHARPIF }
  | "#include" { SHARPINCLUDE }
  | "#print" { SHARPPRINT }
  | "#then" { SHARPTHEN }
  | "#undefine" { SHARPUNDEFINE }
  | "$arr_t" { DOLLARARRT }
  | "$arr_vt" { DOLLARARRVT }
  | "$decrypt" { DOLLARDECRYPT }
  | "$delay" { DOLLARDELAY }
  | "$dynload" { DOLLARDYNLOAD }
  | "$effmask_all" { DOLLAREFFMASK_ALL }
  | "$effmask_exn" { DOLLAREFFMASK_EXN }
  | "$effmask_ref" { DOLLAREFFMASK_REF }
  | "$encrypt" { DOLLARENCRYPT }
  | "$exec" { DOLLAREXEC }
  | "$extype" { DOLLAREXTYPE }
  | "$extval" { DOLLAREXTVAL }
  | "$fold" { DOLLARFOLD }
  | "$force" { DOLLARFORCE }
  | "$lst_t" { DOLLARLSTT }
  | "$lst_vt" { DOLLARLSTVT }
  | "$parallet" { DOLLARPARALLEL }
  | "$raise" { DOLLARRAISE }
  | "$rec_t" { DOLLARRECT }
  | "$rec_vt" { DOLLARRECVT }
  | "$tup_t" { DOLLARTUPT }
  | "$tup_vt" { DOLLARTUPVT }
  | "$unfold" { DOLLARUNFOLD }
  | "$typeof" { DOLLARTYPEOF }
  | "(*" { Loc.set_the_comment_start_position lexbuf; comment lexbuf; token lexbuf }
  | "////" { process_comment_rest_start lexbuf; comment_rest lexbuf; EOF }
  | "//" { comment_line lexbuf; token lexbuf }
  | identifier { process_alphanum_identifier lexbuf }
  | identifier_lbracket { process_array_identifier lexbuf }
  | identifier_lessthan { process_template_identifier lexbuf }
  | symbolic_1 + { process_symbolic_identifier lexbuf }
  | symbolic_2 + { process_symbolic_identifier lexbuf }
  | int_literal { process_int_literal lexbuf }
  | lint_literal { process_lint_literal lexbuf }
  | uint_literal { process_uint_literal lexbuf }
  | float_literal { process_float_literal lexbuf }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "'(" { QUOTELPAREN }
  | "'[" { QUOTELBRACKET }
  | "'{" { QUOTELBRACE }
  | "@(" { ATLPAREN }
  | "@[" { ATLBRACKET }
  | "@{" { ATLBRACE }
  | "#(" { HASHLPAREN }
  | "#[" { HASHLBRACKET }
  | "#{" { HASHLBRACE }
  | "$(" { DOLLARLPAREN }
  | "$[" { DOLLARLBRACKET }
  | "${" { DOLLARLBRACE }  
  | "," { COMMA }
  | ";" { SEMICOLON }
  | "\\" { BACKSLASH }
  | "|-" { BARMINUS } (* meta-programming syntax *)
  | "|-[" { BARMINUSLBRACKET } (* meta-programming syntax *)
  | "`(" { BACKQUOTELPAREN } (* macro syntax *)
  | ",(" { COMMALPAREN } (* macro syntax *)
  | "`[" { BACKQUOTELBRACKET } (* meta-programming syntax *)
  | ",[" { COMMALBRACKET } (* meta-programming syntax *)
  | "`{" { BACKQUOTELBRACE } (* distributed meta-programming syntax *)
  | ",{" { COMMALBRACE } (* distributed meta-programming syntax *)
  | '\'' { char lexbuf }
  | blanks { token lexbuf }
  | newline { process_newline lexbuf; token lexbuf }
  | '"' { Loc.set_the_string_start_position lexbuf; string lexbuf }
  | "%{^" { Loc.set_the_extern_start_position lexbuf; extern 0 lexbuf }
  | "%{" { Loc.set_the_extern_start_position lexbuf; extern 1 lexbuf }
  | "%{$" { Loc.set_the_extern_start_position lexbuf; extern 2 lexbuf }
  | eof { EOF }
  | _ { process_illegal_token lexbuf }

and comment = parse
  | "(*" { process_comment_open (); comment lexbuf }
  | "*)" { process_comment_close comment lexbuf }
  | newline { process_newline lexbuf; comment lexbuf }
  | eof { process_unclosed_comment () }
  | _ { comment lexbuf }

and comment_line = parse
  | [^ '\n']* newline { process_newline lexbuf }

and comment_rest = parse
  | newline { process_newline lexbuf; comment_rest lexbuf }
  | eof { () }
  | _ { comment_rest lexbuf }

and char = parse
  | [^ '\\'] '\'' { process_char lexbuf }
  | '\\' escaped_char '\'' { process_escaped_char lexbuf }
  | '\\' digit_oct digit_oct digit_oct '\'' { process_char_oct_3 lexbuf }
  | '\\' digit_oct digit_oct '\'' { process_char_oct_2 lexbuf }
  | '\\' digit_oct '\'' { process_char_oct_1 lexbuf }
  | '\\' xX digit_hex digit_hex '\'' { process_char_hex_2 lexbuf }
  | '\\' xX digit_hex '\'' { process_char_hex_1 lexbuf }
  | _ { process_illegal_char lexbuf }

and string = parse
  | '\"' {  Loc.set_the_string_end_position lexbuf; Lstring (get_the_string ()) }

  | '\\' newline { process_newline lexbuf; string lexbuf }

  | '\\' escaped_char
      { store_escaped_char lexbuf; string lexbuf }

  | '\\' digit_oct digit_oct digit_oct
      { store_char_oct_3 lexbuf; string lexbuf }
  | '\\' digit_oct digit_oct 
      { store_char_oct_2 lexbuf; string lexbuf }
  | '\\' digit_oct
      { store_char_oct_1 lexbuf; string lexbuf }

  | '\\' xX digit_hex digit_hex
      { store_char_hex_2 lexbuf; string lexbuf }
  | '\\' xX digit_hex
      { store_char_hex_1 lexbuf; string lexbuf }

  | newline { process_newline lexbuf; string lexbuf }

  | eof { process_unclosed_string () }

  | _ { store_char lexbuf; string lexbuf }

and extern i = parse
  | "%}" { Loc.set_the_extern_end_position lexbuf; Lextern (i, get_the_string ()) }
  | newline { process_newline lexbuf; store_char lexbuf; extern i lexbuf }
  | eof { process_unclosed_extern () }
  | _ { store_char lexbuf; extern i lexbuf }

(* ****** ****** *)

(* end of [ats_lexer.mll] *)
