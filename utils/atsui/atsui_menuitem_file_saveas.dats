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
overload gint with gint_of_GtkResponseType

(* ****** ****** *)

fun dialog_saveas_errmsg
  {l1,l2:agz} (
    parent: !GtkWindow_ref l1, msg: !gstring l2
  ) : void = () where {
//
  val flags = GTK_DIALOG_DESTROY_WITH_PARENT
  val _type = GTK_MESSAGE_ERROR
  val buttons = GTK_BUTTONS_OK
//
  val dialog = gtk_message_dialog_new0 (flags, _type, buttons, msg)
//
  val (fpf_x | x) = (gs)"SaveAs: Error"
  val () = gtk_window_set_title (dialog, x)
  prval () = fpf_x (x)
//
  val () = gtk_window_set_transient_for (dialog, parent)
//
  val response = gtk_dialog_run (dialog)
  val () = gtk_widget_destroy0 (dialog)
//
  val () = case+ 0 of
    | _ when response = (gint)GTK_RESPONSE_OK => () | _ => () // good as well
  // end of [val]
} // end of [dialog_saveas_errmsg]

(* ****** ****** *)

fun dialog_saveas {l:agz} (
    dialog: !GtkFileChooserDialog_ref l, err: &int
  ) : gstring0 = filename where {
  val () = (print (#LOCATION + ": cb_saveas_activate"); print_newline ())
  val (fpf_chooser | chooser) = gtk_file_chooser_dialog_get_chooser (dialog)
  var filename: gstring0 = gtk_file_chooser_get_filename (chooser)
  prval () = minus_addback (fpf_chooser, chooser | dialog)
  val p = ptr_of_gstring (filename)
  val () = if p > null then dialog_saveas_main (dialog, filename, err)
} // end of [dialog_saveas]

and dialog_saveas_main {l:agz} (
    dialog: !GtkFileChooserDialog_ref l, filename: &gstring1, err: &int
  ) : void = () where {
(*
  val () = printf (
    "dialog_saveas: filename= %s\n", @(__cast filename)
  ) where {
    extern castfn __cast (x: !gstring1): string
  } // end of [val]
*)
  val (pfopt_fil | p_fil) =
    fopen_err (__cast filename, file_mode_w)
  where {
    extern castfn __cast (x: !gstring1): string
  } // end of [val]
//
  val () = if (p_fil > null) then let
    prval Some_v pf_fil = pfopt_fil
    val (fpf_tv | tv) = topenv_get_textview_source ()
    val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
//
    val () = $UT.gtk_text_buffer_store_file (file_mode_lte_w_w | tb, !p_fil)
    val () = gtk_text_buffer_set_modified (tb, GFALSE)
    val () = topenv_textview_source_update_statusbar ()
//
    val (fpf_srcwin | srcwin) = $SWL.the_srcwinlst_search_textbuf (tb)
    val p_srcwin = $SWL.ptr_of_srcwin (srcwin)
    val () = if p_srcwin > null then let
      val () = $SWL.srcwin_set_nsaved (srcwin, 0)
      val [l1:addr] (pf, fpf | p) = $SWL.srcwin_getref_name (srcwin)
      val sgn = compare_gstring_gstring (!p, filename)
      val () = case+ :(pf: gstring1 @ l1) => 0 of
        | _ when sgn <> 0 => let // name change
            val () = $SWL.srcwin_set_menuitm_label (srcwin, filename)
            val tmp = !p
          in
            !p := filename; filename := tmp
          end // end of [sgn = 0]
        | _ => ()
      // end of [val]
      prval () = minus_addback (fpf, pf | srcwin)
    in
      // nothing
    end // end of [val]
    prval () = fpf_srcwin (srcwin)
    prval () = minus_addback (fpf_tb, tb | tv)
    prval () = fpf_tv (tv)
    val _err = fclose_err (pf_fil | p_fil)
    val () = assert_prerrf_bool1 (_err = 0, "%s: %s", @(#LOCATION, "[fclose] failed"))
    prval None_v () = pf_fil
  in
    // nothing
  end else let
    prval None_v () = pfopt_fil in err := err + 1
  end (* end of [if] *)
} // end of [dialog_saveas_main]

(* ****** ****** *)

implement
cb_file_saveas_activate () = GTRUE where {
(*
  val () = (print (#LOCATION + ": cb_saveas_activate"); print_newline ())
*)
  val dialog = gtk_file_chooser_dialog_new
    (stropt_some "ATSUI: Save As", GTK_FILE_CHOOSER_ACTION_SAVE)
//
  val (fpf_x | x) = (gs)GTK_STOCK_CANCEL
  val (fpf_btn | btn) = gtk_dialog_add_button (dialog, x, GTK_RESPONSE_CANCEL)
  prval () = fpf_x (x)
  prval () = minus_addback (fpf_btn, btn | dialog)
//
  val (fpf_x | x) = (gs)GTK_STOCK_SAVE
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
  val (fpf_chooser | chooser) = gtk_file_chooser_dialog_get_chooser (dialog)
  val (fpf_srcwin | srcwin) = $SWL.the_srcwinlst_get_current ()
  val p_srcwin = $SWL.ptr_of_srcwin (srcwin)
  val () = if (p_srcwin > null) then let
    val nsaved = $SWL.srcwin_get_nsaved (srcwin)
    val (fpf_name | name) = $SWL.srcwin_get_name (srcwin)
    val () = if nsaved >= 0 then let
      // HX-2010-05-10: why is the next line alone not enough?
      val _gboolean = gtk_file_chooser_set_filename (chooser, name)
      val (fpf_base | base) = $UT.filename_get_basename (name)
      val () = gtk_file_chooser_set_current_name (chooser, base)
      prval () = minus_addback (fpf_base, base | name)
    in
      // nothing
    end else let
      val () = gtk_file_chooser_set_current_name (chooser, name)
    in
      // nothing
    end // end of [val]
    prval () = minus_addback (fpf_name, name | srcwin)
  in
    // nothing
  end // end of [val]
  prval () = fpf_srcwin (srcwin)
  val () = gtk_file_chooser_set_do_overwrite_confirmation (chooser, GTRUE)
  prval () = minus_addback (fpf_chooser, chooser | dialog)
//
  var err: int = 0
  val response = gtk_dialog_run (dialog)
  val () = case+ 0 of
    | _ when (
        response = (gint)GTK_RESPONSE_ACCEPT
      ) => let
        val filename = dialog_saveas (dialog, err)
        val () = case+ 0 of
        | _ when (err = 0) =>
            topenv_container_source_update_label ()
          // end of [_ when ...]
        | _ => () where {
            val msg = g_strdup_printf (
              "ERROR: the file [%s] cannot be opened.", @(__cast filename)
            ) where {
              extern castfn __cast {l:addr} (x: !gstring l): string
            } // end of [val]
            val (fpf_win | win) = gtk_dialog_get_window (dialog)
            val () = dialog_saveas_errmsg (win, msg)
            prval () = minus_addback (fpf_win, win | dialog)
            val () = gstring_free (msg)
          } // end of [_]
      in
        gstring_free (filename)
      end // end of [GTK_RESPONSE_ACCEPT]
    | _ when (
        response = (gint)GTK_RESPONSE_CLOSE
      ) => ()
    | _ when (
        response = (gint)GTK_RESPONSE_DELETE_EVENT
      ) => ()
    | _ => () // HX: should the user be asked again?
  // end of [val]
  val () = gtk_widget_destroy (dialog)
  val () = g_object_unref (dialog)
} // end of [cb_file_saveas_activate]

(* ****** ****** *)

(* end of [atsui_menuitem_file_saveas.dats] *)
