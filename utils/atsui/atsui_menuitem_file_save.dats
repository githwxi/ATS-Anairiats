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

implement
cb_file_save_activate () = GTRUE where {
  val (fpf_srcwin | srcwin) = $SWL.the_srcwinlst_get_current ()
  val p_scrwin = $SWL.ptr_of_srcwin (srcwin)
  val () = assert_errmsg (p_scrwin > null, #LOCATION + ": [scrwin] is NULL")
  val nsaved = $SWL.srcwin_get_nsaved (srcwin)
  val _ = (
if (nsaved >= 0) then let
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
  val isModified = gtk_text_buffer_get_modified (tb)
  val isModified = (bool_of)isModified
  val () = if isModified then let
    val (fpf_name | name) = $SWL.srcwin_get_name (srcwin)
    val (pfopt_fil | p_fil) =
      fopen_err (__cast name, file_mode_w)
    where {
      extern castfn __cast {l:agz} (x: !gstring l): string
    } // end of [val]
    val () = if (p_fil > null) then let
      prval Some_v pf_fil = pfopt_fil
//
      val () = $UT.gtk_text_buffer_store_file (file_mode_lte_w_w | tb, !p_fil)
      val () = gtk_text_buffer_set_modified (tb, GFALSE)
      val () = topenv_textview_source_update_statusbar ()
//
      val _err = fclose_err (pf_fil | p_fil)
      val () = assert_prerrf_bool1 (_err = 0, "%s: %s", @(#LOCATION, "[fclose] failed"))
      prval None_v () = pf_fil
      val () = $SWL.srcwin_set_nsaved (srcwin, nsaved + 1)
    in
      // nothing
    end else let
      prval None_v () = pfopt_fil
    in
      // nothing
    end (* end of [if] *)
    prval () = minus_addback (fpf_name, name | srcwin)
  in
    // nothing
  end // end of [val]
  prval () = minus_addback (fpf_tb, tb | tv)
  prval () = fpf_tv (tv)
in
  GTRUE
end else // nsaved = -1
  cb_file_saveas_activate ()
) : gboolean // end of [if]
// end of [val]
  prval () = fpf_srcwin (srcwin)
} // end of [cb_file_save_activate]

(* ****** ****** *)

(* end of [atsui_menuitem_file_save.dats] *)
