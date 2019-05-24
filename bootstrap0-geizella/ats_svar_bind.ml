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

module Err = Ats_error
module Loc = Ats_location

(* ****** ****** *)

type loc = Loc.location

let error (msg: string): 'a = Err.error ("ats_svar_bind: " ^ msg)

(* ****** ****** *)

type svar_map = sexp2 SvarMap.t

(* ****** ****** *)

let the_svar_map: svar_map ref = ref (SvarMap.empty)
let the_svar_map_list: (svar_map list) ref = ref []

let svar_map_get (): svar_map = !the_svar_map
						
let svar_add (s2v: svar2) (s2e: sexp2): unit =
(*
  let () =
    Printf.printf "svar_add: %a -> %a\n" fprint_svar2 s2v fprint_sexp2 s2e in
*)
  the_svar_map := SvarMap.add s2v s2e !the_svar_map

let svar_add_list (bds: (svar2 * sexp2) list): unit =
  List.iter (function (s2v, s2e) -> svar_add s2v s2e) bds

let svar_find (s2v: svar2): sexp2 option =
  try Some (SvarMap.find s2v !the_svar_map) with Not_found -> None

let pop (): unit =
  match !the_svar_map_list with
    | svm :: svms -> (the_svar_map := svm; the_svar_map_list := svms)
    | [] -> error "pop"

let push (): unit = (the_svar_map_list := !the_svar_map :: !the_svar_map_list)

let depth (): int = List.length (!the_svar_map_list)

(* ****** ****** *)

let initialize (): unit = begin
  the_svar_map := SvarMap.empty;
  the_svar_map_list := [];
end

(* ****** ****** *)

(* end of [ats_svar_bind] *)
