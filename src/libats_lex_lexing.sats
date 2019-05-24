(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
// July 2007
//
(* ****** ****** *)

abstype accept_table_t // boxed type

fun __accept_table_make
  (nton: int) (nitm: int) (s: string): accept_table_t
fun __accept_table_free (acctbl: accept_table_t): void
fun accept_table_get
  (acctbl: accept_table_t, nstate: int): int (* irule *)

(* ****** ****** *)

abstype transition_table_t // boxed type

fun __transition_table_make (n: int) (s: string): transition_table_t
fun __transition_table_free (transtbl: transition_table_t): void
fun transition_table_get // c >= -1
  (transtbl: transition_table_t, nstate: int, c: int): int (* nstate *)

(* ****** ****** *)

abstype position_t // boxed type

typedef lint = int_long_t0ype
fun position_line (p: position_t):<> int
fun position_loff (p: position_t):<> int
fun position_toff (p: position_t):<> lint

(* ****** ****** *)

fun lt_position_position (p1: position_t, p2: position_t):<> bool
overload < with lt_position_position
fun lte_position_position (p1: position_t, p2: position_t):<> bool
overload <= with lte_position_position

fun eq_position_position (p1: position_t, p2: position_t):<> bool
overload = with eq_position_position
fun neq_position_position (p1: position_t, p2: position_t):<> bool
overload <> with neq_position_position

(* ****** ****** *)

fun fprint_position {m:file_mode}
  (pf: file_mode_lte (m, w) | fil: &FILE m, pos: position_t): void
overload fprint with fprint_position
fun print_position (pos: position_t): void = "lexing_print_position"
overload print with print_position
fun prerr_position (pos: position_t): void = "lexing_prerr_position"
overload prerr with prerr_position

(* ****** ****** *)

abstype infile_t (view) // boxed type for the input file

fun infile_free {v:view}
  (pf: v | f: infile_t v): void = "lexing_infile_free"
fun infile_getc {v:view}
  (pf: !v | f: infile_t v): int = "lexing_infile_getc"
fun infile_make_string (s: string): [v:view] (v | infile_t v)

fun infile_make_file {m:file_mode} {l:addr}
  (pf_fil: FILE m @ l, pf_mod: file_mode_lte (m, r) | fil: ptr l)
  : [v:view] (v | infile_t v)
fun infile_make_stdin (): [v:view] (v | infile_t v)

(* ****** ****** *)

absviewt@ype lexbuf_t (* implemented externally in lexing.dats*)

(* ****** ****** *)
//
// HX: implemented externally in lexing.dats
//
fun lexbuf_fstpos_get
  (lb: &lexbuf_t): position_t = "lexbuf_fstpos_get"
fun lexbuf_fstpos_set (lb: &lexbuf_t): void = "lexbuf_fstpos_set"

fun lexbuf_lstpos_get
  (lb: &lexbuf_t): position_t = "lexbuf_lstpos_get"
fun lexbuf_lstpos_set (lb: &lexbuf_t): void = "lexbuf_lstpos_set"

fun lexbuf_curpos_get
  (lb: &lexbuf_t): position_t = "lexbuf_curpos_get"
fun lexbuf_curpos_set (lb: &lexbuf_t): void = "lexbuf_curpos_set"

fun lexbuf_size_get (lb: &lexbuf_t): Nat = "lexbuf_size_get"
fun lexbuf_char_next (lb: &lexbuf_t): int = "lexbuf_char_next"
fun lexbuf_is_eof (lb: &lexbuf_t): bool = "lexbuf_is_eof"

fun
lexing_engine_lexbuf (
  lb: &lexbuf_t, transtbl: transition_table_t, acctbl: accept_table_t
) : int (*nstate*)
  = "lexing_engine_lexbuf"
// end of [fun]

(* ****** ****** *)
//
// HX: this function makes a lexbuf from an infile.
//
fun lexbuf_make_infile
  {v:view} (
  pf: v | f: infile_t v
) : [l:addr] (
  lexbuf_t @ l | ptr l
) = "lexbuf_make_infile"

//
// HX: this function frees a lexbuf.
//
fun lexbuf_free
  {l:addr} (
  pf: lexbuf_t @ l | p: ptr l
) : void
  = "lexbuf_free"
// end of [fun]

(* ****** ****** *)
//
// HX: this function gets the default lexbuf.
//
fun lexing_lexbuf_get
  (): [l:addr] (lexbuf_t @ l | ptr l)
  = "lexing_lexbuf_get"

//
// HX: this function sets the default lexbuf.
//
fun lexing_lexbuf_set
  {l:addr} (pf: lexbuf_t @ l | p: ptr l): void
  = "lexing_lexbuf_set"

//
// HX: this function frees the default lexbuf.
//
fun lexing_lexbuf_free (): void = "lexing_lexbuf_free"

fun lexing_engine (
  transtbl: transition_table_t, acctbl: accept_table_t
) : int = "lexing_engine"

(* ****** ****** *)

fun lexeme_get_lexbuf (
  lb: &lexbuf_t, index: int
) : char = "lexeme_get_lexbuf"
fun lexeme_get (index: int): char = "lexeme_get"

fun lexeme_set_lexbuf (
  lb: &lexbuf_t, index: int, c: char
) : void = "lexeme_set_lexbuf"
fun lexeme_set (index: int, c: char): void = "lexeme_set"

fun lexeme_string_lexbuf
  (lb: &lexbuf_t): string = "lexeme_string_lexbuf"
fun lexeme_string (): string = "lexeme_string"

fun lexeme_lint_lexbuf (
  lb: &lexbuf_t, base: int
) : lint = "lexeme_lint_lexbuf"
fun lexeme_lint (base: int): lint = "lexeme_lint"

//
// HX: this function is for reading out an integer from the lexbuf.
//
fun lexeme_int (base: int): int = "lexeme_int"

(* ****** ****** *)
//
// HX: this function is for testing whether the lexbuf reaches the end.
//
fun lexing_is_eof (): bool = "lexing_is_eof"

(* ****** ****** *)

fun lexing_fstpos_get (): position_t = "lexing_fstpos_get"
fun lexing_lstpos_get (): position_t = "lexing_lstpos_get"
fun lexing_curpos_get (): position_t = "lexing_curpos_get"

fun lexing_curpos_prerr (): void = "lexing_curpos_prerr"

(* ****** ****** *)

exception LexingErrorException
//
// HX: this function reports a lexing error by raising the exception
// [LexingErrorException]
//
fun lexing_error {a:viewt@ype} (): a

(* ****** ****** *)

(* end of [libats_lex_lexing.sats] *)
