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

open Ats_staexp2
open Ats_dynexp2

module Err = Ats_error
module Sym = Ats_symbol
module Syn = Ats_syntax

module SEXP = Ats_staexp2
module DEXP = Ats_dynexp2
module SEnv2 = Ats_staenv2
module SDEnv2 = Ats_stadynenv2

(* ****** ****** *)

let error (s: string): 'a = begin
  prerr_string "ats_name_space: "; Err.error s;
end

(* ****** ****** *)

type name = Sym.symbol

let make_name (s: string) = Sym.make_with_string s

module type NameSpaceType = sig
  val add: name -> unit
  val add_list: name list -> unit

  val get_names: unit -> name list
  val get_all_names: unit -> name list

  val localjoin: unit -> unit

  val pop: unit -> unit
  val push: unit -> unit

  val restore: unit -> unit
  val save: unit -> unit

  val initialize: unit -> unit
end

module NameSpace: NameSpaceType = struct

  let the_names: name list ref = ref []
  let the_names_list: name list list ref = ref []
  let the_saved_list: (name list * name list list) list ref = ref []

  let add (n: name) = begin
    the_names := n :: !the_names
  end (* end of [add] *)

  let add_list (ns: name list) = begin
    the_names := List.append ns (!the_names)
  end (* end of [add_list] *)

  let get_names (): name list = !the_names
  let get_all_names (): name list = begin
    List.concat (!the_names :: !the_names_list)
  end (* end of [get_all_names] *)

  let initialize (): unit = begin
    the_names := []; the_names_list := [];
  end (* end of [initialize] *)

  let localjoin () = match !the_names_list with
    | _ :: ns :: nss -> begin
	the_names := !the_names @ ns;
	the_names_list := nss;
      end
    | _ -> error "localjoin: the_names_list contains too few elements!"
  (* end of [localjoin] *)

  let pop (): unit = begin
    match !the_names_list with
      | ns :: nss -> (the_names := ns; the_names_list := nss)
      | [] -> error "pop: the_names_list is empty!"
  end (* end of [pop] *)

  let push (): unit = begin
    the_names_list := !the_names :: !the_names_list; the_names := [];
  end (* end of [push] *)

  let save (): unit = begin
    the_saved_list := (!the_names, !the_names_list) :: !the_saved_list;
    the_names := [];
    the_names_list := [];
  end

  let restore (): unit =
    match !the_saved_list with
      | (ns, nss) :: rest -> begin
	  the_names := ns;
	  the_names_list := nss;
	  the_saved_list := rest;
	end
      | _ -> error "restore: the_saved_list is empty!"
  (* end of [resotre] *)

end

(* ****** ****** *)

type stadynenv =
    SEnv2.SRT2env.table * SEnv2.SEXP2env.table * SDEnv2.DEXP2env.table * DEXP.dec2 list

type stadynenv_map = (stadynenv) Sym.SymMap.t

let the_stadynenv_map: stadynenv_map ref = ref (Sym.SymMap.empty)

let stadynenv_find (n: name): stadynenv option =
  Sym.sym_find n !the_stadynenv_map

let stadynenv_add (n: name) (env: stadynenv): unit =
  (the_stadynenv_map := Sym.SymMap.add n env !the_stadynenv_map)

(* ****** ****** *)

let srt2_env_find (id: Sym.symbol): SEXP.srtext2 option =
  let rec aux = function
    | [] -> SEnv2.SRT2env.find_in_pervasives id
    | n :: ns -> begin
	match stadynenv_find n with
	  | None -> aux ns
	  | Some (env, _, _, _) -> begin
	      match SEnv2.SRT2env.table_find id env with
		| None -> aux ns
		| ans -> ans
	    end
      end in
    aux (NameSpace.get_all_names ())
(* end of [srt2_env_find] *)

let sexp2_env_find (id: Sym.symbol): sitem2 option =
  let rec aux = function
    | [] -> SEnv2.SEXP2env.find_in_pervasives id
    | n :: ns -> begin
	match stadynenv_find n with
	  | None -> aux ns
	  | Some (_, env, _, _) -> begin
	      match SEnv2.SEXP2env.table_find id env with
		| None -> aux ns
		| ans -> ans
	    end
      end in
    aux (NameSpace.get_all_names ())
(* end of [sexp2_env_find] *)

let dexp2_env_find (id: Sym.symbol): ditem2 option =
  let rec aux = function
    | [] -> SDEnv2.DEXP2env.find_in_pervasives id
    | n :: ns -> begin
	match stadynenv_find n with
	  | None -> aux ns
	  | Some (_, _, env, _) -> begin
	      match SDEnv2.DEXP2env.table_find id env with
		| None -> aux ns
		| ans -> ans
	    end
      end in
    aux (NameSpace.get_all_names ())
(* end of [dexp2_env_find] *)

(* ****** ****** *)

let initialize () = begin
  NameSpace.initialize ();
  the_stadynenv_map := Sym.SymMap.empty;
end

(* ****** ****** *)

(* end of [ats_name_space.ml] *)
