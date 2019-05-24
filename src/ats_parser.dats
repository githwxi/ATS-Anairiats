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
// Time: August 2007
//
(* ****** ****** *)

%{^
#include "libc/CATS/stdio.cats" // for [atslib_fopen_exn]
%} // end of [%{^]

(* ****** ****** *)

extern
fun fopen_exn {m:file_mode}
  (s: string, m: file_mode m)
  : [l:addr] (FILE m @ l | ptr l) = "atslib_fopen_exn"
// end of [fopen_exn]

(* ****** ****** *)

staload Syn = "ats_syntax.sats"
typedef i0de = $Syn.i0de
typedef s0exp = $Syn.s0exp and d0exp = $Syn.d0exp

(* ****** ****** *)

staload "ats_parser.sats"

(* ****** ****** *)

staload LEXING = "libats_lex_lexing.sats"

(* ****** ****** *)

extern // implemented in [ats_grammar.yats]
fun yyparse_main (tok0: token_t): yyres = "yyparse_main"
// end of [yyparse_main]

(* ****** ****** *)

fn flag_is_sta (flag: int): bool = (flag = 0)
fn flag_is_dyn (flag: int): bool = (flag > 0)

(* ****** ****** *)

local
//
// HX: these functions are needed in [ats_grammar.yats] 
//
extern
fun yyres_i0de
  (id: i0de): yyres = "atsopt_yyres_i0de"
implement yyres_i0de (id) = YYRESi0de (id)

extern
fun yyres_s0exp
  (s0e: s0exp): yyres = "atsopt_yyres_s0exp"
implement yyres_s0exp (s0e) = YYRESs0exp (s0e)

extern
fun yyres_d0exp
  (d0e: d0exp): yyres = "atsopt_yyres_d0exp"
implement yyres_d0exp (d0e) = YYRESd0exp (d0e)

extern
fun yyres_d0eclst
  (d0cs: d0eclst): yyres = "atsopt_yyres_d0eclst"
implement yyres_d0eclst (d0cs) = YYRESd0eclst (d0cs)

in // in of [local]
//
// HX: nothing
//
end // end of [local]

(* ****** ****** *)

implement
token_of_yybeg (tok) =
  case+ tok of
  | YYBEGnone () => $Lex.YYBEG_none
//
  | YYBEGi0de () => $Lex.YYBEG_i0de
  | YYBEGs0rtid () => $Lex.YYBEG_s0rtid
  | YYBEGsi0de () => $Lex.YYBEG_si0de
  | YYBEGdi0de () => $Lex.YYBEG_di0de
//
  | YYBEGs0exp () => $Lex.YYBEG_s0exp
  | YYBEGd0exp () => $Lex.YYBEG_d0exp
  | YYBEGd0ecseq_sta () => $Lex.YYBEG_d0ecseq_sta
  | YYBEGd0ecseq_dyn () => $Lex.YYBEG_d0ecseq_dyn
// end of [token_of_yybeg]

(* ****** ****** *)

implement
parse_from_stdin_yyres
  (tok0) = yyres where {
//
  val tok0: token_t = token_of_yybeg (tok0)
//
  val (pf_infil | p_infil) = $LEXING.infile_make_stdin ()
  val (pf_lexbuf | lexbuf) =
    $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
//
  val yyres = yyparse_main (tok0)
//
  val () = $LEXING.lexing_lexbuf_free ()
//
} // end of [parse_from_stdin_yyres]

implement
parse_from_stdin_d0eclst
  (flag) = d0cs where {
//
  var tok0: yybeg = YYBEGnone ()
//
  val () = if flag_is_sta flag then tok0 := YYBEGd0ecseq_sta ()
  val () = if flag_is_dyn flag then tok0 := YYBEGd0ecseq_dyn ()
//
  val yyres = parse_from_stdin_yyres (tok0)
  val- YYRESd0eclst (d0cs) = yyres
//
} // end of [parse_from_stdin_d0eclst]

(* ****** ****** *)

implement
parse_from_filename_yyres
  (tok0, filename) = yyres where {
(*
  val () = begin
    print "parse_from_filename_yyres: ";
    $Fil.print_filename (filename);
    print_newline ();
  end // end of [val]
*)
//
  val tok0: token_t = token_of_yybeg (tok0)
//
  val fullname = $Fil.filename_full filename
  val file_mode_r = $extval (file_mode r, "\"r\"")
  val (pf_fil | p_fil) = fopen_exn (fullname, file_mode_r)
  val (pf_infil | p_infil) =
    $LEXING.infile_make_file (pf_fil, file_mode_lte_r_r | p_fil)
  val (pf_lexbuf | lexbuf) =
    $LEXING.lexbuf_make_infile (pf_infil | p_infil)
  val () = $LEXING.lexing_lexbuf_set (pf_lexbuf | lexbuf)
//
  val yyres = yyparse_main (tok0)
  val () = $LEXING.lexing_lexbuf_free ()
} // end of [parse_from_filename_yyres]

implement
parse_from_filename_d0eclst
  (flag, filename) = d0cs where {
//
  var tok0: yybeg = YYBEGnone ()
//
  val () = if flag_is_sta flag then tok0 := YYBEGd0ecseq_sta ()
  val () = if flag_is_dyn flag then tok0 := YYBEGd0ecseq_dyn ()
//
  val yyres = parse_from_filename_yyres (tok0, filename)
//
  val- YYRESd0eclst (d0cs) = yyres
//
} // end of [parse_from_filename_d0eclst]

(* ****** ****** *)

(* end of [ats_parser.dats] *)
