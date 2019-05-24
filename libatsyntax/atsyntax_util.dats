(*
**
** Some utility functions for handling the syntax of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Guillaume Bruneri (guillaume.bruneri AT gmail DOT com)
**
** Start Time: February, 2011
**
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // there is no need for dynloading at run-time
#define ATS_DYNLOADFUN_NAME "atsyntax_initialize"

(* ****** ****** *)

staload "atsyntax_util.sats"

(* ****** ****** *)

local

staload "ats_label.sats"
staload "ats_symbol.sats"

in // in of [local]

implement
tostring_label (l) = let
  val ans = $Lab.label_get_int (l)
in
  case+ ans of
  | ~Some_vt (i) => tostring_int (i)
  | ~None_vt () => let
      val ans = label_get_sym (l) in case+ ans of
      | ~Some_vt s => symbol_name (s) | ~None_vt () => "" (*deadcode*)
    end // end of [None_vt]
end // end of [tostring_label]

end // end of [local]

(* ****** ****** *)

local

staload "ats_parser.sats"
staload LEXING = "libats_lex_lexing.sats"

extern // implemented in [ats_grammar.yats]
fun yyparse_main (tok0: token_t): yyres = "yyparse_main"

in // in of [local]

implement
parse_from_string_yyres
  (tok0, inp) = yyres where {
  val tok0 = token_of_yybeg (tok0)
  val (pf_infil | p_infil) = $LEXING.infile_make_string (inp)
  val (pf_lexbuf | lexbuf) = $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
  val yyres = yyparse_main (tok0)
  val () = $LEXING.lexing_lexbuf_free ()
} // end of [parse_from_string_yyres]

implement
parse_from_string_i0de (inp) = id where {
  val- YYRESi0de (id) = parse_from_string_yyres (YYBEGi0de, inp)
} // end of [parse_from_string_i0de]

implement
parse_from_string_s0rtid (inp) = id where {
  val- YYRESi0de (id) = parse_from_string_yyres (YYBEGs0rtid, inp)
} // end of [parse_from_string_s0rtid]

implement
parse_from_string_si0de (inp) = id where {
  val- YYRESi0de (id) = parse_from_string_yyres (YYBEGsi0de, inp)
} // end of [parse_from_string_si0de]

implement
parse_from_string_di0de (inp) = id where {
  val- YYRESi0de (id) = parse_from_string_yyres (YYBEGdi0de, inp)
} // end of [parse_from_string_di0de]

implement
parse_from_string_s0exp (inp) = s0e where {
  val- YYRESs0exp (s0e) = parse_from_string_yyres (YYBEGs0exp, inp)
} // end of [parse_from_string_s0exp]

implement
parse_from_string_d0exp (inp) = d0e where {
  val- YYRESd0exp (d0e) = parse_from_string_yyres (YYBEGd0exp, inp)
} // end of [parse_from_string_d0exp]

implement
parse_from_string_d0ecseq_dyn (inp) = d0cs where {
  val- YYRESd0eclst (d0cs) = parse_from_string_yyres (YYBEGd0ecseq_dyn, inp)
} // end of [parse_from_string_d0eclst]

end // end of [local]

(* ****** ****** *)

(* end of [atsyntax_util.dats] *)
