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
// Time: April 2010
//
(* ****** ****** *)

staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

dynload "atsui_util.dats"
dynload "atsui_srcwinlst.dats"

dynload "atsui_compile.dats"
//
dynload "atsui_menu_file.dats"
dynload "atsui_menuitem_file_openfile.dats"
dynload "atsui_menuitem_file_save.dats"
dynload "atsui_menuitem_file_saveas.dats"
dynload "atsui_menuitem_file_quit.dats"
//
dynload "atsui_menu_edit.dats"
dynload "atsui_menuitem_edit_undoredo.dats"
//
dynload "atsui_menu_view.dats"
dynload "atsui_menuitem_view_fontsel.dats"
//
dynload "atsui_menu_winlst.dats"
//
dynload "atsui_textview_source.dats"
dynload "atsui_textview_source_linenumber.dats"
dynload "atsui_textview_output.dats"
//
dynload "atsui_topenv.dats"

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

extern fun main1 (): void = "main1"
implement
main1 () = () where {
   val () = topenv_init ()
   val (fpf_topwin | topwin) = topenv_get_topwin ()
   val () = gtk_widget_show (topwin)
   prval () = fpf_topwin (topwin)
   val () = gtk_main () // looping until [gtk_main_quit] is called
} // end of [main1]

(* ****** ****** *)

%{$
ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  gtk_init ((int*)&argc, (char***)&argv) ;
  main1 () ;
  return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [atsui_main.dats] *)
