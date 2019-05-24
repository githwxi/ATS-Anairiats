(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2010-201? Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May, 2010
//
(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"
macdef gs = gstring_of_string

(* ****** ****** *)

%{^

/* ****** ****** */

ats_ptr_type
atsui_topenv_get_textview_output () {
  return theATSUItopenv.textview_output ;
} // end of [atsui_topenv_get_textview_output]

ats_void_type
atsui_topenv_initset_textview_output
  (ats_ptr_type x) {
  if (theATSUItopenv.textview_output != (GtkTextView*)0) {
    fprintf (stderr, "exit(ATS): [atsui_topenv_initset_textview_output] failed\n"); exit(1);
  } // end of [if]
  theATSUItopenv.textview_output = (GtkTextView*)x ;
} // end of [atsui_topenv_initset_textview_output]

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

macdef TEXTVIEW_OUTPUT_LEFT_MARGIN = 6

extern
fun topenv_make_textview_output (): GtkTextView_ref1
  = "atsui_topenv_make_textview_output"
implement
topenv_make_textview_output () = let
  val tb = gtk_text_buffer_new_null ()
  val [l_tv:addr] tv = gtk_text_view_new_with_buffer (tb)
  val () = gtk_text_view_set_editable (tv, GFALSE)
  val () = gtk_text_view_set_cursor_visible (tv, GFALSE)
  val () = gtk_text_view_set_left_margin (tv, (gint)TEXTVIEW_OUTPUT_LEFT_MARGIN)
//
  val (fpf_x | x) = (gs)"(No compilation output yet)"  
  val () = gtk_text_buffer_setall_text (tb, x)
  prval () = fpf_x (x)
//
  val () = g_object_unref (tb)
in
  tv (* return *)
end // end of [topenv_make_textview_output]

(* ****** ****** *)

(* end of [atsui_textview_output.dats] *)
