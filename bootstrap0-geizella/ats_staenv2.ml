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

(* static environment *)

module Err = Ats_error
module Fil = Ats_filename
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol
module SymEnv = Ats_symenv
module Syn = Ats_syntax

module P = Printf

open Ats_staexp2

(* some type abbreviations *)

type loc = Loc.location
type symbol = Sym.symbol

(* a standard error reporting functions *)

let error (s: string): 'a = Err.error ("Ats_staenv2: " ^ s)

(* sort environment *)

module SRT2arg: sig type item end with type item = srtext2 = struct
  type item = srtext2
end (* end of [SRT2arg] *)

module SRT2env: SymEnv.SymEnvType with type item = srtext2 =
  SymEnv.SymEnvFun (SRT2arg)

let srt2_env_add_var (s2tv: srt2_var): unit = 
  let s = Syn.sym_of_sid s2tv.srt2_var_name in
    SRT2env.add s (STE2srt (SRT2var s2tv))

let srt2_env_add_var_list (s2tvs: srt2_var list): unit =
  List.iter srt2_env_add_var s2tvs

(* ************ *)

module SEXP2arg
  : sig type item end with type item = sitem2 = struct
  type item = sitem2
end (* end of [SEXP2arg] *)

module SEXP2env: SymEnv.SymEnvType with type item = sitem2 =
  SymEnv.SymEnvFun (SEXP2arg)

(* ****** ****** *)

let sexp2_env_add_cst_list (id: Syn.sid) (s2cs: scst2 list): unit = 
  let s = Syn.sym_of_sid id in SEXP2env.add s (SI2cst s2cs)

let sexp2_env_add_datcon (d2c: dcon2): unit =
  let s = Syn.sym_of_did d2c.dcon2_name in SEXP2env.add s (SI2datcon d2c)

let sexp2_env_add_fil (id: Syn.sid) (f: Fil.filename): unit =
  let s = Syn.sym_of_sid id in SEXP2env.add (Sym.staload_symbol s) (SI2fil f)
(* end of [sexp2_env_add_fil] *)

let sexp2_env_add_mod
  (id: Syn.sid) (ls2vs: labsvar2 list) (s2e: sexp2): unit =
  let s = Syn.sym_of_sid id in SEXP2env.add s (SI2mod (ls2vs, s2e))
(* end of [sexp2_env_add_mod] *)

let sexp2_env_add_var (s2v: svar2): unit = begin
  SEXP2env.add (Syn.sym_of_sid s2v.svar2_name) (SI2var s2v)
end (* end of [sexp2_env_add_var] *)

let sexp2_env_add_var_list (s2vs: svar2 list): unit =
  List.iter sexp2_env_add_var s2vs
(* end of [sexp2_env_add_var_list] *)

(* ****** ****** *)

(* end of [ats_staenv2.ml] *)
