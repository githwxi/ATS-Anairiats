# 40 "ats_printf_c.mll"
 
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

# 126 "ats_printf_c.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\253\255\001\000\002\000\003\000\009\000\010\000\255\255\
    \020\000\000\000\030\000\040\000\022\000\000\000\000\000\046\000\
    \254\255";
  Lexing.lex_backtrk = 
   "\001\000\255\255\001\000\000\000\255\255\000\000\000\000\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \255\255";
  Lexing.lex_default = 
   "\002\000\000\000\002\000\255\255\255\255\255\255\255\255\000\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\016\000\
    \000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\003\000\004\000\002\000\
    \002\000\005\000\000\000\000\000\005\000\000\000\010\000\000\000\
    \005\000\000\000\000\000\000\000\005\000\000\000\005\000\000\000\
    \000\000\005\000\007\000\008\000\008\000\008\000\008\000\008\000\
    \008\000\008\000\008\000\008\000\008\000\008\000\008\000\008\000\
    \008\000\008\000\008\000\008\000\008\000\008\000\007\000\011\000\
    \011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
    \011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
    \011\000\011\000\007\000\000\000\000\000\000\000\000\000\000\000\
    \007\000\000\000\000\000\000\000\007\000\000\000\000\000\007\000\
    \000\000\000\000\000\000\007\000\007\000\007\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\014\000\000\000\
    \007\000\000\000\013\000\000\000\000\000\000\000\007\000\000\000\
    \000\000\000\000\007\000\000\000\000\000\000\000\000\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\000\000\007\000\
    \000\000\000\000\000\000\000\000\000\000\007\000\007\000\000\000\
    \000\000\007\000\000\000\007\000\000\000\000\000\007\000\007\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\255\255";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\002\000\003\000\
    \004\000\005\000\255\255\255\255\005\000\255\255\009\000\255\255\
    \005\000\255\255\255\255\255\255\005\000\255\255\005\000\255\255\
    \255\255\005\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\008\000\008\000\008\000\008\000\
    \008\000\008\000\008\000\008\000\008\000\008\000\010\000\010\000\
    \010\000\010\000\010\000\010\000\010\000\010\000\010\000\010\000\
    \011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
    \011\000\011\000\012\000\255\255\255\255\255\255\255\255\255\255\
    \014\000\255\255\255\255\255\255\013\000\255\255\255\255\015\000\
    \255\255\255\255\255\255\015\000\015\000\015\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\012\000\255\255\
    \012\000\255\255\012\000\255\255\255\255\255\255\015\000\255\255\
    \255\255\255\255\012\000\255\255\255\255\255\255\255\255\015\000\
    \012\000\015\000\015\000\015\000\015\000\015\000\255\255\015\000\
    \255\255\255\255\255\255\255\255\255\255\015\000\015\000\255\255\
    \255\255\015\000\255\255\015\000\255\255\255\255\015\000\015\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\002\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\015\000";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec translate ts lexbuf =
    __ocaml_lex_translate_rec ts lexbuf 0
and __ocaml_lex_translate_rec ts lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 167 "ats_printf_c.mll"
        ( (let t = flags lexbuf in translate (t :: ts) lexbuf) )
# 239 "ats_printf_c.ml"

  | 1 ->
# 168 "ats_printf_c.mll"
                      ( translate ts lexbuf )
# 244 "ats_printf_c.ml"

  | 2 ->
# 169 "ats_printf_c.mll"
        ( ts )
# 249 "ats_printf_c.ml"

  | 3 ->
# 170 "ats_printf_c.mll"
      ( raise Illegal_printf_c_string )
# 254 "ats_printf_c.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_translate_rec ts lexbuf __ocaml_lex_state

and flags lexbuf =
    __ocaml_lex_flags_rec lexbuf 5
and __ocaml_lex_flags_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let flags_arg = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 173 "ats_printf_c.mll"
                                                      ( width flags_arg lexbuf )
# 267 "ats_printf_c.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_flags_rec lexbuf __ocaml_lex_state

and width flags_arg lexbuf =
    __ocaml_lex_width_rec flags_arg lexbuf 6
and __ocaml_lex_width_rec flags_arg lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let width_arg = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 176 "ats_printf_c.mll"
                            ( precision flags_arg width_arg lexbuf )
# 280 "ats_printf_c.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_width_rec flags_arg lexbuf __ocaml_lex_state

and precision flags_arg width_arg lexbuf =
    __ocaml_lex_precision_rec flags_arg width_arg lexbuf 9
and __ocaml_lex_precision_rec flags_arg width_arg lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let prec_arg = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 179 "ats_printf_c.mll"
                                ( length flags_arg width_arg prec_arg lexbuf )
# 293 "ats_printf_c.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_precision_rec flags_arg width_arg lexbuf __ocaml_lex_state

and length flags_arg width_arg prec_arg lexbuf =
    __ocaml_lex_length_rec flags_arg width_arg prec_arg lexbuf 12
and __ocaml_lex_length_rec flags_arg width_arg prec_arg lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let length_arg = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 183 "ats_printf_c.mll"
      ( specifier flags_arg width_arg prec_arg length_arg lexbuf )
# 306 "ats_printf_c.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_length_rec flags_arg width_arg prec_arg lexbuf __ocaml_lex_state

and specifier flags_arg width_arg prec_arg length_arg lexbuf =
    __ocaml_lex_specifier_rec flags_arg width_arg prec_arg length_arg lexbuf 15
and __ocaml_lex_specifier_rec flags_arg width_arg prec_arg length_arg lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let spec_arg = Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 188 "ats_printf_c.mll"
      ( (printf_c_output flags_arg width_arg prec_arg length_arg spec_arg) )
# 319 "ats_printf_c.ml"

  | 1 ->
# 189 "ats_printf_c.mll"
      ( raise Illegal_printf_c_string )
# 324 "ats_printf_c.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_specifier_rec flags_arg width_arg prec_arg length_arg lexbuf __ocaml_lex_state

;;

# 191 "ats_printf_c.mll"
 
  let printf_c_string_parse (s: string): (printf_c_argtype list) option =
    try let lexbuf = Lexing.from_string s in Some (List.rev (translate [] lexbuf))
    with Illegal_printf_c_string -> None

# 336 "ats_printf_c.ml"
