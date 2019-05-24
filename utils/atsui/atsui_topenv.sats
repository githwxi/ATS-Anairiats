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
// Time: April 2010

(* ****** ****** *)

%{#
#include "atsui.cats"
%} // end of [%{#] 

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

fun topenv_init (): void
fun topenv_fini (): void

(* ****** ****** *)

fun topenv_initset_topwin (x: GtkWindow_ref1): void
  = "atsui_topenv_initset_topwin"
// end of [topenv_initset_topwin]

fun topenv_get_topwin ()
  : [l:agz] (GtkWindow_ref l -<lin,prf> void | GtkWindow_ref l)
  = "atsui_topenv_get_topwin"
// end of [topenv_get_topwin]

(* ****** ****** *)

fun topenv_get_aclgrp ()
  : [l:agz] (GtkAccelGroup_ref l -<lin,prf> void | GtkAccelGroup_ref l)
  = "atsui_topenv_get_aclgrp"
// end of [topenv_get_aclgrp]

(* ****** ****** *)

fun topenv_get_vbox0 ()
  : [l:agz] (GtkVBox_ref l -<lin,prf> void | GtkVBox_ref l)
  = "atsui_topenv_get_vbox0"
// end of [topenv_get_vbox0]

(* ****** ****** *)

fun topenv_make_menu_file (): GtkMenu_ref1
fun topenv_get_menu_file ()
  : [l:agz] (GtkMenu_ref l -<lin,prf> void | GtkMenu_ref l)
  = "atsui_topenv_get_menu_file"
// end of [topenv_get_menu_file]

fun topenv_get_menuitem_file_close ()
  : [l:agz] (GtkMenuItem_ref l -<lin,prf> void | GtkMenuItem_ref l)
  = "atsui_topenv_get_menuitem_file_close"
// end of [topenv_get_menuitem_file_close]

fun topenv_get_menuitem_file_save ()
  : [l:agz] (GtkMenuItem_ref l -<lin,prf> void | GtkMenuItem_ref l)
  = "atsui_topenv_get_menuitem_file_save"
// end of [topenv_get_menuitem_file_save]

fun topenv_get_menuitem_file_saveas ()
  : [l:agz] (GtkMenuItem_ref l -<lin,prf> void | GtkMenuItem_ref l)
  = "atsui_topenv_get_menuitem_file_saveas"
// end of [topenv_get_menuitem_file_saveas]

(* ****** ****** *)

fun topenv_make_menu_edit (): GtkMenu_ref1

fun topenv_get_menuitem_edit_cut ()
  : [l:agz] (GtkMenuItem_ref l -<lin,prf> void | GtkMenuItem_ref l)
  = "atsui_topenv_get_menuitem_edit_cut"
// end of [topenv_get_menuitem_edit_cut]

fun topenv_get_menuitem_edit_copy ()
  : [l:agz] (GtkMenuItem_ref l -<lin,prf> void | GtkMenuItem_ref l)
  = "atsui_topenv_get_menuitem_edit_copy"
// end of [topenv_get_menuitem_edit_copy]

fun topenv_get_menuitem_edit_paste ()
  : [l:agz] (GtkMenuItem_ref l -<lin,prf> void | GtkMenuItem_ref l)
  = "atsui_topenv_get_menuitem_edit_paste"
// end of [topenv_get_menuitem_edit_paste]

(* ****** ****** *)

fun topenv_make_menu_view (): GtkMenu_ref1

fun topenv_get_menuitem_view_fontsel ()
  : [l:agz] (GtkCheckMenuItem_ref l -<lin,prf> void | GtkCheckMenuItem_ref l)
  = "atsui_topenv_get_menuitem_view_fontsel"
// end of [topenv_get_menuitem_view_fontsel]

fun topenv_get_menuitem_view_linenumber ()
  : [l:agz] (GtkCheckMenuItem_ref l -<lin,prf> void | GtkCheckMenuItem_ref l)
  = "atsui_topenv_get_menuitem_view_linenumber"
// end of [topenv_get_menuitem_view_linenumber]

(* ****** ****** *)

fun topenv_make_menu_window (): GtkMenu_ref1

fun topenv_get_menu_window ()
  : [l:agz] (GtkMenu_ref l -<lin,prf> void | GtkMenu_ref l)
  = "atsui_topenv_get_menu_window"
// end of [topenv_get_menu_window]

(* ****** ****** *)

fun topenv_get_container_source ()
  : [l:agz] (GtkFrame_ref l -<lin,prf> void | GtkFrame_ref l)
  = "atsui_topenv_get_container_source"
// end of [topenv_get_container_source]

fun topenv_container_source_set_label {l:agz} (name: !gstring l): void
fun topenv_container_source_update_label (): void

(* ****** ****** *)

fun topenv_get_textview_source_initset_flag (): int
  = "atsui_topenv_get_textview_source_initset_flag"
// end of [topenv_get_textview_source_initset_flag]

fun the_drawarea_welcome_fini (): void
fun topenv_initset_textview_source_if (): void

fun topenv_get_textview_source ()
  : [l:agz] (GtkTextView_ref l -<lin,prf> void | GtkTextView_ref l)
  = "atsui_topenv_get_textview_source"
// end of [topenv_get_textview_source]

(* ****** ****** *)

fun topenv_textview_source_update_statusbar (): void
fun cb_textview_source_mark_changed (): gboolean
fun cb_textview_source_modified_changed (): gboolean

(* ****** ****** *)

fun cb_textview_source_expose_event_linenumber
  {c:cls | c <= GtkTextView} {l:agz}
  (tv: !gobjref (c, l), event: &GdkEventExpose) : gboolean
// end of [cb_textview_source_expose_event_linenumber]

(* ****** ****** *)

fun topenv_get_container_output ()
  : [l:agz] (GtkTextView_ref l -<lin,prf> void | GtkTextView_ref l)
  = "atsui_topenv_get_container_output"
// end of [topenv_get_container_output]

fun topenv_get_textview_output ()
  : [l:agz] (GtkTextView_ref l -<lin,prf> void | GtkTextView_ref l)
  = "atsui_topenv_get_textview_output"
// end of [topenv_get_textview_output]

(* ****** ****** *)

fun topenv_get_statusbar ()
  : [l:agz] (GtkStatusbar_ref l -<lin,prf> void | GtkStatusbar_ref l)
  = "atsui_topenv_get_statusbar"
// end of [topenv_get_statusbar]

(* ****** ****** *)

fun topenv_menu_window_append
  {c:cls | c <= GtkTextBuffer} {l1,l2:agz}
  (filename: !gstring l1, tb: !gobjref (c, l2))
  : GtkMenuItem_ref1
// end of [topenv_menu_window_append]

fun topenv_menu_window_remove
  {c:cls | c <= GtkMenuItem} {l:agz} (item: !gobjref (c, l)): void
// end of [topenv_menu_window_remove]

(* ****** ****** *)

fun cb_file_openfile_activate (): gboolean
fun cb_file_save_activate (): gboolean // callback for the [save] menuitem
fun cb_file_saveas_activate (): gboolean // callback for the [saveas] menuitem
fun cb_file_quit_activate (): gboolean // callback for the [quit] menuitem

(* ****** ****** *)

fun cb_view_fontsel_activate (): gboolean
fun cb_view_linenumber_activate (): gboolean

(* ****** ****** *)

fun cb_compile_clicked_if (): gboolean // callback for the [compile] button

(* ****** ****** *)

(* end of [atsui_topenv.sats] *)
