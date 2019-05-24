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

open Ats_misc
open Ats_syntax
open Ats_staexp1

module Fix = Ats_fixity
module Sym = Ats_symbol
module SymEnv = Ats_symenv

(* ****** ****** *)

type symbol = Sym.symbol
type fixity = Fix.fixity

module FixityEnv = SymEnv.SymEnvFun (struct type item = Fix.fixity end)

let fixity_add_opr id fx = FixityEnv.add (sym_of_id id) fx

let fixity_find_opr_sym (s: symbol): fixity option =
  match FixityEnv.find s with
    | None -> FixityEnv.find_in_pervasives s 
    | ans -> ans

let fixity_find_opr id = fixity_find_opr_sym (sym_of_id id)

let fixity_find_srt_opr id = fixity_find_opr_sym (sym_of_srt_id id)

let fixity_find_sexp_opr id = fixity_find_opr_sym  (sym_of_sid id)

let fixity_find_dexp_opr id = fixity_find_opr_sym (sym_of_did id)

(* ****** ****** *)

module E0xpEnv = SymEnv.SymEnvFun (struct type item = e0xp1 end)

let e0xp1_add_id id e = E0xpEnv.add (sym_of_id id) e
let e0xp1_find_sym s = E0xpEnv.find s
let e0xp1_find_id id = E0xpEnv.find (sym_of_id id)

(* ****** ****** *)

let env_pop () = begin
  FixityEnv.pop ();
end

let env_push () = begin
  FixityEnv.push ();
end

let env_save () = begin
  FixityEnv.save (); E0xpEnv.save ();
end

let env_restore () = begin
  FixityEnv.restore (); E0xpEnv.restore ()
end

let env_localjoin () = begin
  FixityEnv.localjoin ();
end

let env_make_top_pervasive () =  begin
  FixityEnv.make_top_pervasive ();
  E0xpEnv.make_top_pervasive ();
end

(* ****** ****** *)

(* end of [ats_env1.ml] *)

