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

module Err = Ats_error
module Loc = Ats_location

module SExp2 = Ats_staexp2

(* ****** ****** *)

type loc = Loc.location

(* ****** ****** *)

let error (msg: string): 'a = Err.error ("ats_svar_stamp: " ^ msg)

(* ****** ****** *)

type svar2 = SExp2.svar2
type stamp = SExp2.stamp and stamps = SExp2.stamps

exception EmptyStampsList

let the_stamps: stamps ref = ref (SExp2.Stamps.empty)
let the_stamps_list: (stamps list) ref = ref []

let svar2_stamp (s2v: svar2): stamp = s2v.SExp2.svar2_stamp

let svar_add (s2v: svar2): unit =
(*
  let () =
    Printf.fprintf stdout "ats_svar_stamp: svar_add: s2v = %a\n"
      SExp2.fprint_svar2 s2v in
*)
  (the_stamps := SExp2.Stamps.add (svar2_stamp s2v) !the_stamps)

let svar_list_add (s2vs: svar2 list): unit = List.iter svar_add s2vs

(* ****** ****** *)

let stamp_remove (stamp: stamp): unit =
(*
  let () =
    Printf.fprintf stdout "ats_svar_stamp: svar_remove: s2v = %a\n"
      SExp2.fprint_svar2 s2v in
*)
  (the_stamps := SExp2.Stamps.remove stamp !the_stamps)

(* ****** ****** *)

let stamps_get (): stamps = !the_stamps
let stamps_set (ss: stamps): unit = the_stamps := ss

let pop (): unit =
  match !the_stamps_list with
    | stamps :: stampss ->
	(the_stamps := stamps; the_stamps_list := stampss)
    | [] -> raise EmptyStampsList
(* end of [pop] *)

let push (): unit = begin
  the_stamps_list := !the_stamps :: !the_stamps_list
end (* end of [push] *)

let restore (): unit = pop ()

let save (): unit = begin
  the_stamps_list := !the_stamps :: !the_stamps_list;
  the_stamps := SExp2.Stamps.empty
end (* end of [save] *)

(* ****** ****** *)

let initialize (): unit = begin
  the_stamps := SExp2.Stamps.empty;  the_stamps_list := []
end (* end of [initialize] *)

(* ****** ****** *)

(* end of [ats_svar_stamp.ml] *)
