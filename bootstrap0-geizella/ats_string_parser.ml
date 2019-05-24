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

module P = Printf
module PFats = Ats_printf_ats
module Sym = Ats_symbol
module Syn = Ats_syntax

type symbol = Sym.symbol

let the_parfun_map: (string -> string option) Sym.SymMap.t ref =
  ref Sym.SymMap.empty

let parfun_find (id: Syn.id): (string -> string option) option =
  Sym.sym_find (Syn.sym_of_id id) !the_parfun_map

let parfun_add
  (k: symbol) (f: string -> string option): unit =
  the_parfun_map := (Sym.SymMap.add k f !the_parfun_map)
(* end of [parfun_add] *)

(* handling file mode strings *)

let mode_symbol = Sym.make_with_string "mode"
let mode_string_parse (s: string): string option =
  match s with
    | "r" -> Some "file_mode_r" | "r+" -> Some "file_mode_rr"
    | "w" -> Some "file_mode_w" | "w+" -> Some "file_mode_ww"
    | "a" -> Some "file_mode_a" | "a+" -> Some "file_mode_aa"
    | _ -> None
(* end of [mode_string_parse] *)

(* handling ATS format strings for print *)

let format_symbol = Sym.make_with_string "format"
let printf_ats_string_parse (s: string): string option =
  try Some (PFats.printf_ats_string_parse s)
  with PFats.Illegal_printf_ats_string -> None
(* end of [printf_ats_string_parse] *)

(* ****** ****** *)

let initialize (): unit = begin
  the_parfun_map := Sym.SymMap.empty;
  parfun_add mode_symbol mode_string_parse;
  parfun_add format_symbol printf_ats_string_parse;
end (* end of [initialize] *)

(* ****** ****** *)

(* end of [ats_string_parser.ml] *)
