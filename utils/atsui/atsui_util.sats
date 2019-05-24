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

staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

fun gtk_button_new_with_label
  (label: string): GtkButton_ref1 = "mac#atsctrb_gtk_button_new_with_label"
// end of [gtk_button_new_with_label]

fun gtk_frame_new
  (name: string): GtkFrame_ref1 = "mac#atsctrb_gtk_frame_new"
// end of [gtk_frame_new]

fun gtk_menu_item_new_with_label
  (name: string): GtkMenuItem_ref1 = "mac#atsctrb_gtk_menu_item_new_with_label"
// end of [gtk_menu_item_new_with_label]

fun gtk_menu_item_new_with_mnemonic
  (name: string): GtkMenuItem_ref1 = "mac#atsctrb_gtk_menu_item_new_with_mnemonic"
// end of [gtk_menu_item_new_with_mnemonic]

fun gtk_image_menu_item_new_from_stock
  {c:cls | c <= GtkAccelGroup} {l:addr}
  (name: string, aclgrp: !gobjref (c, l)): GtkImageMenuItem_ref1
  = "atsctrb_gtk_image_menu_item_new_from_stock"
// end of [gtk_image_menu_item_new_from_stock]

fun gtk_image_menu_item_new_from_stock_null
  (name: string): GtkImageMenuItem_ref1 = "mac#atsctrb_gtk_image_menu_item_new_from_stock_null"
// end of [gtk_image_menu_item_new_from_stock_null]

(* ****** ****** *)

fun filename_get_basename {l1:agz}
  (x: !gstring l1): [l2:agz] (minus (gstring l1, gstring l2) | gstring l2)
  = "atsui_filename_get_basename"
// end of [filename_get_basename]

(* ****** ****** *)

fun gtk_text_buffer_clear
  {c:cls | c <= GtkTextBuffer} {l:agz} (tb: !gobjref (c, l)): void
// end of [gtk_text_buffer_clear]

(* ****** ****** *)

fun gtk_text_buffer_load_file
  {c:cls | c <= GtkTextBuffer} {l:agz} {m:file_mode}
  (pfmod: file_mode_lte (m, r) | tb: !gobjref (c, l), src: &FILE m): void
// end of [text_buffer_load_file]

(* ****** ****** *)

fun gtk_text_buffer_store_file
  {c:cls | c <= GtkTextBuffer} {l:agz} {m:file_mode}
  (pfmod: file_mode_lte (m, w) | tb: !gobjref (c, l), dst: &FILE m): void
// end of [text_buffer_store_file]

(* ****** ****** *)

(* end of [atsui_util.sats] *)
