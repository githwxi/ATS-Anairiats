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

staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"
stadef srcwin = $SWL.srcwin

(* ****** ****** *)

staload "atsui_topenv.sats"
macdef gs = gstring_of_string
overload gint with gint_of_GtkResponseType

(* ****** ****** *)

macdef GNULL = (gpointer)null

(* ****** ****** *)

fun dialog_openfile_opened
  {l:agz} (x: !srcwin l): void = () where {
//
  val () = printf ("dialog_openfile_opened\n", @())
//
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val (fpf_tb | tb) = $SWL.srcwin_get_textbuf (x)
  val () = gtk_text_view_set_buffer (tv, tb)
  prval () = minus_addback (fpf_tb, tb | x)
  prval () = fpf_tv (tv)
} // end of [dialog_openfile_opened]

fun dialog_openfile_first
  {c:cls | c <= GtkFileChooserDialog} {l:agz}
  (dialog: !gobjref (c, l), filename: gstring1): void = () where {
//
  val () = printf
    ("dialog_openfile_first: filename= %s\n", @(__cast filename)) where {
    extern castfn __cast {l:agz} (x: !gstring l): string
  } // end of [val]
//
  val (pfopt_fil | p_fil) =
    fopen_err (__cast filename, file_mode_r) where {
    extern castfn __cast {l:agz} (x: !gstring l): string
  } // end of [val]
//
  val () = if (p_fil > null) then let
    prval Some_v pf_fil = pfopt_fil
    val (fpf_tv | tv) = topenv_get_textview_source ()
    val () = gtk_text_view_set_editable (tv, GTRUE)
    val () = gtk_text_view_set_cursor_visible (tv, GTRUE)
//
    val tb = gtk_text_buffer_new_null ()
    val _sid = g_signal_connect
      (tb, (gsignal)"mark-set", G_CALLBACK(cb_textview_source_mark_changed), GNULL)
    val _sid = g_signal_connect
      (tb, (gsignal)"mark-deleted", G_CALLBACK(cb_textview_source_mark_changed), GNULL)
    val _sid = g_signal_connect
      (tb, (gsignal)"modified-changed", G_CALLBACK(cb_textview_source_modified_changed), GNULL)
//
    val () = gtk_text_view_set_buffer (tv, tb)
    val () = $UT.gtk_text_buffer_load_file (file_mode_lte_r_r | tb, !p_fil)
//
    val () = gtk_text_buffer_set_modified (tb, GFALSE)
    val _true = cb_textview_source_modified_changed ()
//
    val item = topenv_menu_window_append (filename, tb)
    val srcwin = $SWL.srcwin_make (filename, tb, item)
    val () = $SWL.srcwin_set_nsaved (srcwin, 0) // the default is -1
    val () = $SWL.the_srcwinlst_append (srcwin)
    val _err = fclose_err (pf_fil | p_fil)
    val () = assert_prerrf_bool1 (_err = 0, "%s: %s", @(#LOCATION, "[fclose] failed"))
    prval None_v () = pf_fil
    prval () = fpf_tv (tv)
  in
    // nothing
  end else let
    prval None_v () = pfopt_fil
    val () = gstring_free filename
  in
    // nothing
  end (* end of [if] *)
} // end of [dialog_openfile_first]

fun dialog_openfile
  {c:cls | c <= GtkFileChooserDialog} {l:agz}
  (dialog: !gobjref (c, l)): void = let
  val () = (print (#LOCATION + ": dialog_openfile"); print_newline ())
//
  val (fpf_chooser | chooser) = gtk_file_chooser_dialog_get_chooser (dialog)
  val [l_filename:addr] filename = gtk_file_chooser_get_filename (chooser)
  prval () = minus_addback (fpf_chooser, chooser | dialog)
//
  val ptr = ptr_of_gstring filename
in
  if (ptr <> null) then let
    val (fpf_x | x) = $SWL.the_srcwinlst_search_name (filename)
    val px = $SWL.ptr_of_srcwin (x)
  in
    if (px > null) then let
      val () = gstring_free (filename)
      val () = dialog_openfile_opened (x)
      prval () = fpf_x (x)
    in
      // nothing
    end else let
      prval () = fpf_x (x)
    in
      dialog_openfile_first (dialog, filename)
    end // end of [if]
  end else let
    val _null = gstring_free_null (filename)
  in
    // do nothing
  end // end of [if]
end // end of [dialog_openfile]

(* ****** ****** *)

implement
cb_file_openfile_activate () = GTRUE where {
//
  val () = topenv_initset_textview_source_if ()
//
  val dialog = gtk_file_chooser_dialog_new
    (stropt_some "ATSUI: Open File", GTK_FILE_CHOOSER_ACTION_OPEN)
//
  val (fpf_x | x) = (gs)GTK_STOCK_CANCEL
  val (fpf_btn | btn) = gtk_dialog_add_button (dialog, x, GTK_RESPONSE_CANCEL)
  prval () = fpf_x (x)
  prval () = minus_addback (fpf_btn, btn | dialog)
//
  val (fpf_x | x) = (gs)GTK_STOCK_OPEN
  val (fpf_btn | btn) = gtk_dialog_add_button (dialog, x, GTK_RESPONSE_ACCEPT)
  prval () = fpf_x (x)
  prval () = minus_addback (fpf_btn, btn | dialog)
//
  val (fpf_dialogwin | dialogwin) = gtk_dialog_get_window (dialog)
  val (fpf_topwin | topwin) = topenv_get_topwin ()
  val () = gtk_window_set_transient_for (dialogwin, topwin)
  prval () = fpf_topwin (topwin)
  prval () = minus_addback (fpf_dialogwin, dialogwin | dialog)
//
  val response = gtk_dialog_run (dialog)
  val () = case+ 0 of
    | _ when (
        response = (gint)GTK_RESPONSE_ACCEPT
      ) => let
        val () = dialog_openfile (dialog) // processing the selected file
      in
        topenv_container_source_update_label ()
      end // end of [GTK_RESPONSE_ACCEPT]
    | _ when (
        response = (gint)GTK_RESPONSE_CLOSE
      ) => ()
    | _ => ()
  // end of [val]
//
  val () = gtk_widget_destroy0 (dialog)
//
} // end of [cb_file_openfile_activate]

(* ****** ****** *)

(* end of [atsui_menuitem_file_openfile.dats] *)
