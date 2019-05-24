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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May 2010

(* ****** ****** *)

staload STDIO = "libc/SATS/stdio.sats"
staload STDLIB = "libc/SATS/stdlib.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"

(* ****** ****** *)

extern
fun load_compile_output (filename: string): void

implement
load_compile_output (filename) = let
//
  val (pfopt_fil | p_fil) = $STDIO.fopen_err (filename, file_mode_r)
//
in // in of [let]
//
if (p_fil > null) then let
  prval Some_v pf_fil = pfopt_fil
  val (fpf_tv | tv) = topenv_get_textview_output ()
  val () = gtk_text_view_set_editable (tv, GFALSE)
  val () = gtk_text_view_set_cursor_visible (tv, GFALSE)
  val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
  val () = $UT.gtk_text_buffer_load_file (file_mode_lte_r_r | tb, !p_fil)
  prval () = minus_addback (fpf_tb, tb | tv)
  prval () = fpf_tv (tv)
  val _err = $STDIO.fclose_err (pf_fil | p_fil)
  val () = assert_prerrf_bool1 (_err = 0, "%s: %s", @(#LOCATION, "[fclose] failed"))
  prval None_v () = pf_fil
in
  // nothing
end else let
  prval None_v () = pfopt_fil
in
  // nothing
end (* end of [if] *)
//
end // end of [load_compile_output]

(* ****** ****** *)

#define ATSUIccompoutput ".ATSUIccompoutput.txt"

fun cb_compile_clicked
  (): gboolean = GTRUE where {
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
  val (fpf_x | x) = $SWL.the_srcwinlst_search_textbuf (tb)
  prval () = minus_addback (fpf_tb, tb | tv)
  prval () = fpf_tv (tv)
  val px = $SWL.ptr_of_srcwin (x)
  val () = if (px > null) then let
    val (fpf_name | name) = $SWL.srcwin_get_name (x)
    extern castfn __cast {l:agz} (x: !gstring l): string
    val cmd = g_strdup_printf
      ("atscc --typecheck %s >& %s", @(__cast name, ATSUIccompoutput))
(*
    val () = printf ("cb_compile_clicked: %s\n", @(__cast cmd))
*)
    val _err = $STDLIB.system (__cast cmd)
    val () = gstring_free (cmd)
    prval () = minus_addback (fpf_name, name | x)
    val () = load_compile_output (ATSUIccompoutput)
  in
    // nothing
  end // end of [val]
  prval () = fpf_x (x)
} // end of [cb_compile_clicked]

implement
cb_compile_clicked_if () = let
  val tbflag = topenv_get_textview_source_initset_flag ()
in
  if tbflag > 0 then let
    // val () = cb_save_activate () // HX: should it be done automatically?
  in
    cb_compile_clicked ()
  end else GTRUE(*handled*)
end // end of [cb_compile_clicked_if]

(* ****** ****** *)

(* end of [atsui_compile.dats] *)
