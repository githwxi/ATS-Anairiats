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

(* ats_symenv: implementing symbol enviroments *)

(* ****** ****** *)

open Ats_misc

module Sym = Ats_symbol

(* ****** ****** *)

type symbol = Sym.symbol

module type SymEnvType = sig
  type item
  type table

  val add: symbol -> item -> unit
  val add_list: (symbol * item) list -> unit
  val empty: table
  val find: symbol -> item option
  val find_in_pervasives: symbol -> item option
  val get_top: unit -> table
  val initialize: unit -> unit
  val localjoin: unit -> unit
  val make_pervasive: table -> unit
  val make_top_pervasive: unit -> unit
  val pop: unit -> unit
  val push: unit -> unit
  val restore: unit -> unit
  val save: unit -> unit
  val set_top: table -> unit
  val table_find: symbol -> table -> item option
  val top_to_list: unit -> item list
  val all_to_list: unit -> item list
end (* end of EnvType *)

module SymEnvFun (X: sig type item end)
  : SymEnvType with type item = X.item = struct

    exception SymEnvError

    type item = X.item

    module S = Map.Make (Sym.SymOrd)

    type table = X.item S.t
    
    let the_table: table ref = ref S.empty
    let the_table_list: (table list) ref = ref []
    let the_saved_list: (table * table list) list ref = ref []

    let the_pervasive_list: (table list) ref = ref []

    let empty = S.empty

    let get_top () = !the_table
    let set_top (t: table) = (the_table := t)

    let initialize () = begin
      the_table := S.empty;
      the_table_list := [];
      the_saved_list := [];
      the_pervasive_list := [];
    end

    let make_pervasive (t: table) =
      the_pervasive_list := t :: !the_pervasive_list

    let make_top_pervasive () = begin
      the_pervasive_list := !the_table :: !the_pervasive_list;
      the_table := S.empty;
    end

    let save (): unit = begin
      the_saved_list := (!the_table, !the_table_list) :: !the_saved_list;
      the_table := S.empty;
      the_table_list := [];
    end

    let restore (): unit =
      match !the_saved_list with
	| [] -> begin
	    prerr_line "ats_sym_env: restore";
	    raise SymEnvError
	  end
	| (t, ts) :: tts -> begin
	    the_table := t;
	    the_table_list := ts;
	    the_saved_list := tts;
	  end

    let push (): unit = begin
      the_table_list := !the_table :: !the_table_list;
      the_table := S.empty
    end

    let pop (): unit = match !the_table_list with
      | t :: ts -> (the_table := t; the_table_list := ts)
      | [] -> (prerr_line "ats_sym_env: pop"; raise SymEnvError)

    let add (k: symbol) (i: item): unit =
      (the_table := S.add k i (!the_table))

    let add_list (kis: (symbol * item) list): unit =
      the_table :=
      List.fold_left (fun t  (k, i) -> S.add k i t) (!the_table) kis

    let rec find_aux (k: symbol) (t: table) (ts: table list): item option =
      try Some (S.find k t)
      with Not_found -> match ts with
	| [] -> None | t :: ts -> find_aux k t ts

    let find (k: symbol): item option =
      find_aux k (!the_table) (!the_table_list)

    let find_in_pervasives (k: symbol): item option =
      match !the_pervasive_list with
	| [] -> None
	| t :: ts -> find_aux k t ts

    let localjoin (): unit = match !the_table_list with
	| _ :: t :: ts -> begin
	    let t =
	      S.fold
		(fun (k: symbol) (i: item) (t: table) -> S.add k i t)
		t (!the_table) in
	      (the_table := t; the_table_list := ts)
	  end
	| _ -> (prerr_line "ats_sym_env: localjoin"; raise SymEnvError)

    let table_find (k: symbol) (t: table): item option =
      try Some (S.find k t) with Not_found -> None

    let top_to_list (): item list =
      S.fold (fun _ x xs -> x :: xs) !the_table []

    let all_to_list (): item list =
      let rec aux (t: table) (ts: table list) (res: item list)
	: item list =
	let res = S.fold (fun _ x xs -> x :: xs) t res in
	  match ts with [] -> res | t :: ts -> aux t ts res in
	aux (!the_table) (!the_table_list) []

  end
(* end of [module] *)

(* ****** ****** *)

(* end of [ats_symenv.ml] *)
