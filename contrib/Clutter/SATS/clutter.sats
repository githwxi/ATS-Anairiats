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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Start Time: June, 2010
//
(* ****** ****** *)

%{#
#include "contrib/Clutter/CATS/clutter.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

staload GLIB = "contrib/glib/SATS/glib.sats"
stadef gboolean = $GLIB.gboolean
//
stadef gchar = $GLIB.gchar
//
stadef gint (i:int) = $GLIB.gint (i)
stadef gint = $GLIB.gint
stadef gint8 = $GLIB.gint8
stadef gint16= $GLIB.gint16
stadef gint32= $GLIB.gint32
//
stadef guint (i:int) = $GLIB.guint (i)
stadef guint = $GLIB.guint
stadef guint8 = $GLIB.guint8
stadef guint16= $GLIB.guint16
stadef guint32= $GLIB.guint32
//
stadef gfloat = $GLIB.gfloat
stadef gdouble = $GLIB.gdouble
//
stadef gpointer = $GLIB.gpointer
//
stadef gstring = $GLIB.gstring
stadef gstring0 = $GLIB.gstring0
stadef gstring1 = $GLIB.gstring1

(* ****** ****** *)

staload GOBJ = "contrib/glib/SATS/glib-object.sats"
stadef gobjref = $GOBJ.gobjref

(* ****** ****** *)

staload "contrib/Clutter/SATS/clutterclassdec.sats"

(* ****** ****** *)

absview ClutterFree_v (l:addr)

(* ****** ****** *)

(*
viewtypedef ClutterAction_ref (l:addr) = gobjref (ClutterAction, l)
viewtypedef ClutterAction_ref0 = [l:agez] ClutterAction_ref (l)
viewtypedef ClutterAction_ref1 = [l:addr | l > null] ClutterAction_ref (l)
*)

viewtypedef ClutterRectangle_ref (l:addr) = gobjref (ClutterRectangle, l)
viewtypedef ClutterRectangle_ref0 = [l:agez] ClutterRectangle_ref (l)
viewtypedef ClutterRectangle_ref1 = [l:addr | l > null] ClutterRectangle_ref (l)

viewtypedef ClutterStage_ref (l:addr) = gobjref (ClutterStage, l)
viewtypedef ClutterStage_ref0 = [l:agez] ClutterStage_ref (l)
viewtypedef ClutterStage_ref1 = [l:addr | l > null] ClutterStage_ref (l)

(* ****** ****** *)

#include
"contrib/Clutter/SATS/clutter/clutter-action.sats"
#include "contrib/Clutter/SATS/clutter/clutter-actor.sats"
#include "contrib/Clutter/SATS/clutter/clutter-color.sats"
#include "contrib/Clutter/SATS/clutter/clutter-container.sats"
#include "contrib/Clutter/SATS/clutter/clutter-group.sats"
#include "contrib/Clutter/SATS/clutter/clutter-rectangle.sats"
#include "contrib/Clutter/SATS/clutter/clutter-stage.sats"

(* ****** ****** *)

#include "contrib/Clutter/SATS/clutter/clutter-main.sats"

(* ****** ****** *)

(* end of [clutter.sats] *)
