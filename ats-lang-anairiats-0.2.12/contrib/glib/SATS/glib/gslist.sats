(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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

(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "contrib/glib/CATS/glib/gslist.cats"
%}

(* ****** ****** *)

sortdef vwtp = viewtype

(*
** n = 0 if and only if l = null
*)
absviewtype GSList_ptr
  (a:viewtype+, n:int) // = GSList*
viewtypedef GSList_ptr0 (a:vwtp) = [n:nat] GSList_ptr (a, n)
viewtypedef GSList_ptr1 (a:vwtp) = [n:pos] GSList_ptr (a, n)

(* ****** ****** *)

fun g_slist_new_nil
  {a:vwtp} (): GSList_ptr (a, 0) = "mac#atsctrb_g_slist_new_nil"
// end of [g_slist_new_nil]

fun g_slist_free_nil
  {a:vwtp} (xs: GSList_ptr (a, 0)):<> void = "mac#atsctrb_g_slist_free_nil"
// end of [g_slist_free_nil]

(* ****** ****** *)

(* end of [gslist.sats] *)
