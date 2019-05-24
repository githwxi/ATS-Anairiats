(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

staload "posloc.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

typedef filename = @{ filename= string }
assume filename_t = filename

implement filename_make_string (name) = @{
  filename = name
} // end of [filename_make_string]

implement fprint_filename (pf | out, fil) =
  fprint_string (pf | out, fil.filename)

implement print_filename (fil) = print_mac (fprint_filename, fil)
implement prerr_filename (fil) = prerr_mac (fprint_filename, fil)

(* ****** ****** *)

implement filename_none = @{ filename= "" }
implement filename_stdin = @{ filename= "stdin" }

(* ****** ****** *)

local

viewtypedef filenamelst_vt = List_vt (filename)

val the_filenamelst = ref_make_elt<filenamelst_vt> (list_vt_nil)

in // in of [local]

implement filename_push (x) = let
  val (pfbox | p) = ref_get_view_ptr (the_filenamelst)
  prval vbox pf = pfbox
in
  !p := list_vt_cons (x, !p)
end // end of [filename_push]

implement filename_pop () = let
  val (pfbox | p) = ref_get_view_ptr (the_filenamelst)
  prval vbox pf = pfbox
in
  case+ !p of
  | ~list_vt_cons (x, xs) => (!p := xs)
  | list_vt_nil () => fold@ !p where {
      val () = $effmask_ref begin
        prerr "INTERNAL ERROR: filename_pop: empty stack";
        prerr_newline ()
      end // end of [val]
    } // end of [list_vt_nil]
end (* end of [filename_get] *)

implement filename_get () = $effmask_all let
  val (pfbox | p) = ref_get_view_ptr (the_filenamelst)
  prval vbox pf = pfbox
in
  case+ !p of
  | list_vt_cons (x, _) => (fold@ !p; x)
  | list_vt_nil () => (fold@ !p; filename_none)
end // end of [filename_get]

end // end of [local]

(* ****** ****** *)

typedef position = '{ line= int, loff= int, toff= lint }

assume position_t = position

implement position_origin = '{ line = 0, loff= 0, toff= 0L }

implement position_next (pos, c) =
  if (c = '\n') then '{
    line= pos.line + 1, loff= 0, toff= pos.toff + 1L
  } else '{
    line= pos.line, loff= pos.loff + 1, toff= pos.toff + 1L
  } // end of [if]
// end of [position_next]

implement position_line (p) = p.line
implement position_loff (p) = p.loff
implement position_toff (p) = p.toff

implement fprint_position (pf | fil, pos) = fprintf1_exn
  (pf | fil, "%li(line=%i, offs=%i)", @(pos.toff+1L, pos.line+1, pos.loff+1))
implement print_position (pos) = print_mac (fprint_position, pos)
implement prerr_position (pos) = prerr_mac (fprint_position, pos)

implement lt_position_position (p1, p2) = p1.toff < p2.toff
implement lte_position_position (p1, p2) = p1.toff <= p2.toff
implement eq_position_position (p1, p2) = p1.toff = p2.toff
implement neq_position_position (p1, p2) = p1.toff <> p2.toff

(* ****** ****** *)

typedef location = '{
  filename= filename_t // file name
, begpos_line= int
, begpos_loff= int  // beginning char position in a line
, begpos_toff= lint // beginning char position
, endpos_line= int
, endpos_loff= int  // finishing char position in a line
, endpos_toff= lint // finishing char position
} /* end of [location] */

assume location_t = location

implement fprint_location (pf | out, loc) = begin
  fprint_filename (pf | out, loc.filename);
  fprint1_string (pf | out, ": ");
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

implement location_none = '{
  filename= filename_none
, begpos_line= ~1
, begpos_loff= ~1
, begpos_toff= ~1L
, endpos_line= ~1
, endpos_loff= ~1
, endpos_toff= ~1L
} // end of [location_none]

fn location_is_none (loc: location):<> bool = (loc.begpos_toff < 0L)

(* ****** ****** *)

implement location_make (begpos, endpos) = '{
  filename= filename_get ()
, begpos_line= position_line begpos
, begpos_loff= position_loff begpos
, begpos_toff= position_toff begpos
, endpos_line= position_line endpos
, endpos_loff= position_loff endpos
, endpos_toff= position_toff endpos
} // end of [location_make]

(* ****** ****** *)

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

in '{
  filename = loc1.filename
, begpos_line= begpos_line
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

(* end of [posloc.dats] *)
