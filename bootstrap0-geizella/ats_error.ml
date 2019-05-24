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

(* ats_error: declare some functions for reporting errors *)

module Loc = Ats_location

(* ****** ****** *)

type location = Loc.location

exception ErrorException
exception DeadCodeException

let abort (): 'a = (flush stderr; raise ErrorException)

let prompt: string = ">> "

(* warning: reporting an error *)

let warning (msg: string): unit = begin
  prerr_string msg; prerr_newline ();
end (* end of [warning] *)

(* warning_with_loc: reporting a warning with location information *)

let warning_with_loc (loc: location) (msg: string): unit = begin
  Loc.fprint stderr loc;
  prerr_string ": "; prerr_string msg; prerr_newline ();
end (* end of [warning_with_loc] *)

(* error: reporting an error *)

let error msg = begin
  prerr_string msg; prerr_newline (); abort ()
end (* end of [error] *)

(* error_with_loc: reporting an error with location information *)

let error_with_loc loc msg = begin
  Loc.fprint stderr loc;
  prerr_string ": "; prerr_string msg; prerr_newline ();
  abort ()
end (* end of [error_with_loc] *)

(* ****** ****** *)

(* end of [ats_error.ml] *)
