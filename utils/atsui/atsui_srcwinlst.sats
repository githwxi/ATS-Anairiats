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

staload "contrib/glib/SATS/glib.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gtkclassdec.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

absviewtype srcwin (l:addr) // a boxed type
viewtypedef srcwin0 = [l:agez] srcwin (l)
viewtypedef srcwin1 = [l:addr | l > null] srcwin (l)
castfn ptr_of_srcwin {l:addr} (x: !srcwin l):<> ptr l
castfn srcwin_make_null (x: ptr null):<> srcwin null
castfn srcwin_free_null (x: srcwin null):<> ptr null

(* ****** ****** *)

fun srcwin_isnot_null
  {l:addr} (x: !srcwin l): bool (l > null) = "atspre_ptr_isnot_null"
// end of [srcwin_isnot_null]

(* ****** ****** *)

fun srcwin_get_nsaved
  {l:agz} (x: !srcwin l):<> int = "atsui_srcwin_get_nsaved"
// end of [srcwin_get_nsaved]

fun srcwin_set_nsaved
  {l:agz} (x: !srcwin l, nsaved: int): void = "atsui_srcwin_set_nsaved"
// end of [srcwin_set_nsaved]

(* ****** ****** *)

fun srcwin_get_name
  {l:agz} (x: !srcwin l):<> [l1:agz]
  (minus (srcwin l, gstring l1) | gstring l1)
  = "atsui_srcwin_get_name"
// end of [srcwin_get_name]

fun srcwin_getref_name
  {l:agz} (x: !srcwin l):<> [l1:addr]
  (gstring1 @ l1, minus (srcwin l, gstring1 @ l1) | ptr l1)
  = "atsui_srcwin_getref_name"
// end of [srcwin_getref_name]

(* ****** ****** *)

fun srcwin_get_textbuf
  {l:agz} (x: !srcwin l):<> [l1:agz]
  (minus (srcwin l, GtkTextBuffer_ref l1) | GtkTextBuffer_ref l1)
  = "atsui_srcwin_get_textbuf"
// end of [srcwin_get_textbuf]

(* ****** ****** *)

fun srcwin_get_menuitm
  {l:agz} (x: !srcwin l):<> [l1:agz]
  (minus (srcwin l, GtkMenuItem_ref l1) | GtkMenuItem_ref l1)
  = "atsui_srcwin_get_menuitm"
// end of [srcwin_get_menuitm]

fun srcwin_set_menuitm_label {l1,l2:agz}
  (x: !srcwin l1, name: !gstring l2): void = "atsui_srcwin_set_menuitm_label"
// end of [srcwin_set_menuitm_label]

(* ****** ****** *)

fun srcwin_make (
    name: gstring1
  , textbuf: GtkTextBuffer_ref1
  , menuitm: GtkMenuItem_ref1
  ) : srcwin1 = "atsui_srcwin_make"
// end of [srcwin_make]

fun srcwin_free {l:agz} (x: srcwin l): void = "atsui_srcwin_free"

(* ****** ****** *)

fun the_srcwinlst_append (x: srcwin1): void

fun the_srcwinlst_remove {l:agz}
  (textbuf: !GtkTextBuffer_ref l, n: &int? >> int) : srcwin0
// end of [the_srcwinlst_remove]

fun the_srcwinlst_getnext {n:nat} (n: int n)
  : [l:addr] (srcwin l -<lin,prf> void | srcwin l)
// end of [the_srcwinlst_getnext]

(* ****** ****** *)

fun the_srcwinlst_search_name
  {l:agz} (name: !gstring l): [l1:addr] (srcwin l1 -<lin,prf> void | srcwin l1)
// end of [the_srcwinlst_search_name]

fun the_srcwinlst_search_textbuf
  {c:cls | c <= GtkTextBuffer} {l:agz}
  (name: !gobjref (c, l)): [l1:addr] (srcwin l1 -<lin,prf> void | srcwin l1)
// end of [the_srcwinlst_search_textbuf]

(* ****** ****** *)

fun the_srcwinlst_get_current (): [l:addr] (srcwin l -<lin,prf> void | srcwin l)

(* ****** ****** *)

(* end of [atsui_srcwinlst.sats] *)
