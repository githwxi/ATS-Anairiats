(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustful Software, Inc.
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
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: July, 2011
//
(* ****** ****** *)

staload
FIL = "libatsdoc/SATS/libatsdoc_filename.sats"
typedef filename = $FIL.filename

staload
LOC = "libatsdoc/SATS/libatsdoc_location.sats"
stadef location = $LOC.location
stadef position = $LOC.position

(* ****** ****** *)

staload
LBF = "libatsdoc/SATS/libatsdoc_lexbuf.sats"
stadef lexbuf = $LBF.lexbuf

(* ****** ****** *)

datatype
docerr_node =
  | DE_STRING_unclose of ()
  | DE_EXTCODE_unclose of ()
  | DE_FUNARGLST_unclose of ()
  | DE_FUNRES_none of ()
  | DE_FUNRES_unclose of ()
// end of [docerr_node]
typedef docerr = '{
  docerr_loc= location, docerr_node= docerr_node
} // end of [docerr]

fun docerr_make (loc: location, node: docerr_node): docerr

fun the_docerrlst_clear (): void
fun the_docerrlst_add (err: docerr): void

fun the_docerrlst_length (): int
fun fprint_the_docerrlst (out: FILEref): void

(* ****** ****** *)

fun lexbufpos2_docerr
  (buf: &lexbuf, pos0: &position, pos1: &position, node: docerr_node) : void
// end of [lexbufpos2_docerr]

(* ****** ****** *)

datatype
funarg =
  | FAint of string
  | FAident of string
  | FAstrsub of string
  | FAfunres of string
  | FAnil of ()
// end of [funarg]

typedef funarglst = List (funarg)

fun fprint_funarg (out: FILEref, x: funarg): void
fun fprint_funarglst (out: FILEref, xs: funarglst): void

(* ****** ****** *)
//
// HX: knd = 0/1 : tup/lst
//
datatype
tranitm_node =
  | EXTCODE of (string(*code*))
  | FUNCALL of (string(*fnam*), int(*knd*), funarglst, string(*fres*))
// end of [transitm_node]

typedef tranitm = '{
  tranitm_loc= location, tranitm_node= tranitm_node
} // end of [funcall]

fun tranitm_make (loc: location, node: tranitm_node): tranitm

fun fprint_tranitm (out: FILEref, x: tranitm): void

(* ****** ****** *)
//
fun funres_get_prfx (): string // HX: get the prefix for return names
fun funres_set_prfx (prf: string): void // HX: set the prefix for return names
//
fun funcall_get_fres (): string // HX: using a counter to general unique return names
//
(* ****** ****** *)

fun DIGIT_test (c: char): bool
fun IDENTFST_test (c: char): bool
fun IDENTRST_test (c: char): bool

(* ****** ****** *)
//
// HX: f('\n') must be false!
//
fun ftesting_seq0 (
  buf: &lexbuf, pos: &position, f: char -> bool
) : uint // end of [ftesting_seq0]

(* ****** ****** *)

fun testing_spaces
  (buf: &lexbuf, pos: &position): uint
// end of [testing_spaces]

fun testing_literal (
  buf: &lexbuf, pos: &position, lit: string
) : int // end of [testing_literal]

fun testing_ident (buf: &lexbuf, pos: &position): int

(* ****** ****** *)

fun the_tranitmlst_add (x: tranitm): void
fun the_tranitmlst_get (): List_vt (tranitm)

fun fprint_the_tranitmlst (out: FILEref, basename: string): void

(* ****** ****** *)

fun trans_top (out: FILEref, buf: &lexbuf): void

fun trans_extcode
  (buf: &lexbuf, pos0: &position, pos: &position) : void
// end of [trans_extcode]

fun trans_funcall // HX: pos0 is right after the char '#'
  (buf: &lexbuf, pos0: &position, pos: &position) : Option_vt (string(*fres*))
// end of [trans_funcall]

(* ****** ****** *)
//
// HX: tout: txt; dout: dats
//
fun trans_top_from_stdin (tout: FILEref): void
fun trans_top_from_filename (tout: FILEref, fil: filename): void
fun trans_top_from_basename (tout: FILEref, basename: string): void

(* ****** ****** *)

(* end of [atsdoc_translate.sats] *)
