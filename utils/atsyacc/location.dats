(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
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

// Time: February 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* location: Handling location information. *)

(* ****** ****** *)

staload "libats/lex/lexing.sats"

(* ****** ****** *)

staload "location.sats"

(* ****** ****** *)

typedef location = '{
  begpos_line= int
, begpos_loff= int
, begpos_toff= lint // beginning char position
, endpos_line= int
, endpos_loff= int
, endpos_toff= lint // finishing char position
} // end of [location]

assume location_t = location

(* ****** ****** *)

implement location_none = '{
  begpos_line= ~1
, begpos_loff= ~1
, begpos_toff= ~1L
, endpos_line= ~1
, endpos_loff= ~1
, endpos_toff= ~1L
} // end of [location_none]

fn location_is_none (loc: location):<> bool =
  (loc.begpos_toff < 0L)

implement location_make (begpos, endpos) = '{
  begpos_line= position_line begpos
, begpos_loff= position_loff begpos
, begpos_toff= position_toff begpos
, endpos_line= position_line endpos
, endpos_loff= position_loff endpos
, endpos_toff= position_toff endpos
} // end of [location_make]

implement location_end_make (loc) = let
  val line = loc.endpos_line
  val loff = loc.endpos_loff
  val toff = loc.endpos_toff
in '{
  begpos_line= line, begpos_loff= loff, begpos_toff= toff
, endpos_line= line, endpos_loff= loff, endpos_toff= toff
} end // end of [location_end_make]

fn location_combine_main
  (loc1: location, loc2: location):<> location = let
  var begpos_line: int and begpos_loff: int
  var begpos_toff: lint
  var endpos_line: int and endpos_loff: int
  var endpos_toff: lint

  val () =
    if loc1.begpos_toff <= loc2.begpos_toff then begin
      begpos_line := loc1.begpos_line;
      begpos_loff := loc1.begpos_loff;
      begpos_toff := loc1.begpos_toff;
    end else begin
      begpos_line := loc2.begpos_line;
      begpos_loff := loc2.begpos_loff;
      begpos_toff := loc2.begpos_toff;
    end // end of [if]
  // end of [val]

  val () =
    if loc1.endpos_toff >= loc2.endpos_toff then begin
      endpos_line := loc1.endpos_line;
      endpos_loff := loc1.endpos_loff;
      endpos_toff := loc1.endpos_toff; 
    end else begin
      endpos_line := loc2.endpos_line;
      endpos_loff := loc2.endpos_loff;
      endpos_toff := loc2.endpos_toff; 
    end // end of [if]
  // end of [val]

in '{
  begpos_line= begpos_line
, begpos_loff= begpos_loff
, begpos_toff= begpos_toff
, endpos_line= endpos_line
, endpos_loff= endpos_loff
, endpos_toff= endpos_toff
} end // end of [location_combine_main]

implement location_combine (loc1, loc2) = begin
  case+ 0 of
  | _ when location_is_none loc1 => loc2
  | _ when location_is_none loc2 => loc1
  | _ => location_combine_main (loc1, loc2)
end // end of [location_combine]

(* ****** ****** *)

implement location_begpos_toff (loc) = loc.begpos_toff
implement location_endpos_toff (loc) = loc.endpos_toff

implement lte_location_location (loc1, loc2) = begin
  loc1.begpos_toff <= loc2.begpos_toff
end // end of [lte_location_location]

(* ****** ****** *)

implement fprint_location (pf | out, loc) = begin
  fprint1_lint (pf | out, loc.begpos_toff+1L);
  fprint1_string (pf | out, "(line=");
  fprint1_int (pf | out, loc.begpos_line+1);
  fprint1_string (pf | out, ", offs=");
  fprint1_int (pf | out, loc.begpos_loff+1);
  fprint1_string (pf | out, ") -- ");
  fprint1_lint (pf | out, loc.endpos_toff+1L);
  fprint1_string (pf | out, "(line=");
  fprint1_int (pf | out, loc.endpos_line+1);
  fprint1_string (pf | out, ", offs=");
  fprint1_int (pf | out, loc.endpos_loff+1);
  fprint1_string (pf | out, ")");
end // end of [fprint_location]

implement print_location (loc) = print_mac (fprint_location, loc)
implement prerr_location (loc) = prerr_mac (fprint_location, loc)

(* ****** ****** *)

(* end of [location.dats] *)
