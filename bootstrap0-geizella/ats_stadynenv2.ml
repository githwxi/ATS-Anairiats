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

(* static/dynamic environment *)

open Ats_misc

open Ats_staexp2
open Ats_staexp2_util
open Ats_staenv2
open Ats_dynexp2

module P = Printf

module Err = Ats_error
module Lab = Ats_label
module Loc = Ats_location
module Sym = Ats_symbol
module SymEnv = Ats_symenv
module Syn = Ats_syntax


(* some type abbreviations *)

type loc = Loc.location
type symbol = Sym.symbol

(* a standard error reporting functions *)

let error (s: string): 'a = Err.error ("Ats_stadynenv2: " ^ s)

(* ****** ****** *)

module DEXP2arg: sig type item end with type item = ditem2 = struct
  type item = ditem2
end

module DEXP2env: SymEnv.SymEnvType with type item = ditem2 =
  SymEnv.SymEnvFun (DEXP2arg)

let dexp2_env_add_con (d2c: dcon2): unit =
  let id = Syn.sym_of_did d2c.dcon2_name in
    match DEXP2env.find id with
      | Some (DI2con d2cs) -> DEXP2env.add id (DI2con (d2c :: d2cs))
      | _ -> DEXP2env.add id (DI2con [d2c])
(* end of [dexp2_env_add_con] *)

let dexp2_env_add_cst (d2c: dcst2): unit =
  DEXP2env.add (Syn.sym_of_did d2c.dcst2_name) (DI2cst d2c)

let dexp2_env_add_mac (d2m: dmac2): unit =
  DEXP2env.add (Syn.sym_of_did d2m.dmac2_name) (DI2mac d2m)

let dexp2_env_add_sym (id: symbol) (d2i: ditem2): unit =
  match DEXP2env.find id with
    | Some (DI2sym d2is) -> DEXP2env.add id (DI2sym (d2i :: d2is))
    | _ -> DEXP2env.add id (DI2sym [d2i])
(* end of [dexp2_env_add_sym] *)

let dexp2_env_add_var (d2v: dvar2): unit =
  DEXP2env.add (Syn.sym_of_did d2v.dvar2_name) (DI2var d2v)

let dexp2_env_add_var_list (d2vs: dvar2 list): unit =
  List.iter dexp2_env_add_var d2vs

(* ****** ****** *)

let stadynenv2_localjoin () = begin
  SRT2env.localjoin ();
  SEXP2env.localjoin ();
  DEXP2env.localjoin ();
end

let stadynenv2_pop (): unit = begin
  SRT2env.pop ();
  SEXP2env.pop ();
  DEXP2env.pop ();
end

and stadynenv2_push (): unit = begin
  SRT2env.push ();
  SEXP2env.push ();
  DEXP2env.push ();
end

let stadynenv2_save (): unit = begin
  SRT2env.save ();
  SEXP2env.save ();
  DEXP2env.save ();
end

and stadynenv2_restore (): unit = begin
  SRT2env.restore ();
  SEXP2env.restore ();
  DEXP2env.restore ();
end

let stadynenv2_pervasive (): unit = begin
  SRT2env.make_top_pervasive ();
  SEXP2env.make_top_pervasive ();
  DEXP2env.make_top_pervasive ();
end

(* ****** ****** *)

let initialize (): unit = begin
  SRT2env.initialize (); 
  SRT2env.add Sym.symADDR (STE2srt srt2_addr);
  SRT2env.add Sym.symBOOL (STE2srt srt2_bool);
  SRT2env.add Sym.symCHAR (STE2srt srt2_char);
  SRT2env.add Sym.symEFF (STE2srt srt2_eff);
  SRT2env.add Sym.symINT (STE2srt srt2_int);
  SRT2env.add Sym.symRAT (STE2srt srt2_rat);
  SRT2env.add Sym.symREG (STE2srt srt2_reg);
  SRT2env.add Sym.symPROP (STE2srt srt2_prop);
  SRT2env.add Sym.symTYPE (STE2srt srt2_type);
  SRT2env.add Sym.symT0YPE (STE2srt srt2_t0ype);
  SRT2env.add Sym.symVIEW (STE2srt srt2_view);
  SRT2env.add Sym.symVIEWTYPE (STE2srt srt2_viewtype);
  SRT2env.add Sym.symVIEWT0YPE (STE2srt srt2_viewt0ype);
  SRT2env.add Sym.symTYPES (STE2srt srt2_types);
  SRT2env.make_top_pervasive ();

  SEXP2env.initialize ();

  DEXP2env.initialize ();
  DEXP2env.add Sym.symBRACKETS (DI2sym []);
end

(* ****** ****** *)

(* end of [ats_stadynenv2.ml] *)
