(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
// Time: October, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

%{#
#include "gtkglext/CATS/gtk.cats"
%} // end of [%{#]

(* ****** ****** *)

staload GLIB = "contrib/glib/SATS/glib.sats"
stadef gboolean = $GLIB.gboolean

(* ****** ****** *)

staload GOBJ = "contrib/glib/SATS/glib-object.sats"
stadef GObject = $GOBJ.GObject // class constant
stadef gobjref = $GOBJ.gobjref // boxed viewtype

(* ****** ****** *)

(*
void
gtk_gl_init (int *argc, char ***argv);
gboolean
gtk_gl_init_check (int *argc, char ***argv);
gboolean
gtk_gl_parse_args (int *argc, char ***argv);
*)

(* ****** ****** *)

staload "contrib/GTK/SATS/gtkclassdec.sats"

(* ****** ****** *)

staload "gtkglext/SATS/gdk.sats" // for some classdecs

(* ****** ****** *)

(*
GtkGLExt is an extension to GTK which adds OpenGL capabilities to
GtkWidget. Its use is quite simple: use gtk_widget_set_gl_capability to add
OpenGL support to a widget, it will create a OpenGL drawable
(GdkGLDrawable) for the widget, which can be obtained via
gtk_widget_get_gl_drawable. OpenGL rendering context (GdkGLContext) can
also be obtained via gtk_widget_get_gl_context. With GdkGLDrawable and
GdkGLContext, gdk_gl_drawable_gl_begin and gdk_gl_drawable_gl_end can be
called, and OpenGL function calls can be made between those two functions.
*)

(* ****** ****** *)

(*
gboolean
gtk_widget_set_gl_capability (
  GtkWidget *widget
, GdkGLConfig *glconfig
, GdkGLContext *share_list
, gboolean direct
, int render_type
) ; // end of [gtk_widget_set_gl_capability]
*)

fun
gtk_widget_set_gl_capability
  {c:cls | c <= GtkWidget}
  {c1,c2:cls | c1 <= GdkGLConfig; c2 <= GdkGLContext}
  {l:addr} {l1,l2:addr} (
  widget: !gobjref (c, l)
, glconfig: !gobjref (c1, l1)
, sharelst: !gobjref (c2, l2)
, direct: gboolean, rendertyp: int
) : gboolean
  = "mac#atsctrb_gtk_widget_set_gl_capability"
// end of [gtk_widget_set_gl_capability]

(* ****** ****** *)

(*
gboolean
gtk_widget_is_gl_capable (GtkWidget *widget);
*)
fun
gtk_widget_is_gl_capable
  {c:cls | c <= GtkWidget}
  {l:addr} (
  widget: !gobjref (c, l)
) : gboolean
  = "mac#atsctrb_gtk_widget_is_gl_capable"
// end of [gtk_widget_is_gl_capable]

(*
GdkGLConfig*
gtk_widget_get_gl_config (GtkWidget *widget);
*)
fun gtk_widget_get_gl_config 
  {c1:cls | c1 <= GtkWidget}
  {l1:addr} (
  widget: !gobjref (c1, l1)
) : [c2:cls;l2:addr | c2 <= GdkGLConfig] (
  minus (gobjref (c1, l1), gobjref (c2, l2)) | gobjref (c2, l2)
) = "mac#atsctrb_gtk_widget_get_gl_config"
// end of [gtk_widget_get_gl_config]

(* ****** ****** *)

(*
GdkGLContext*
gtk_widget_create_gl_context (
  GtkWidget *widget, GdkGLContext *share_list, gboolean direct, int render_type
) ; // end of [gtk_widget_create_gl_context]
*)
fun
gtk_widget_create_gl_context
  {c1,c2:cls | c1 <= GtkWidget; c2 <= GdkGLContext}
  {l1,l2:addr} (
  widget: !gobjref (c1, l1)
, sharelst: !gobjref (c2, l2), direct: gboolean, rendertyp: int
) : GdkGLContext_ref0
  = "mac#atsctrb_gtk_widget_create_gl_context"
// end of [gtk_widget_create_gl_context]

(* ****** ****** *)

(*
GdkGLContext*
gtk_widget_get_gl_context (GtkWidget *widget);
*)
fun gtk_widget_get_gl_context 
  {c1:cls | c1 <= GtkWidget}
  {l1:addr} (
  widget: !gobjref (c1, l1)
) : [c2:cls;l2:addr | c2 <= GdkGLContext] (
  minus (gobjref (c1, l1), gobjref (c2, l2)) | gobjref (c2, l2)
) = "mac#atsctrb_gtk_widget_get_gl_context"
// end of [gtk_widget_get_gl_context]

(* ****** ****** *)

(*
GdkGLWindow*
gtk_widget_get_gl_window (GtkWidget *widget);
*)
fun gtk_widget_get_gl_window 
  {c1:cls | c1 <= GtkWidget}
  {l1:addr} (
  widget: !gobjref (c1, l1)
) : [c2:cls;l2:addr | c2 <= GdkGLWindow] (
  minus (gobjref (c1, l1), gobjref (c2, l2)) | gobjref (c2, l2)
) = "mac#atsctrb_gtk_widget_get_gl_window"
// end of [gtk_widget_get_gl_window]

(* ****** ****** *)

(*
#define gtk_widget_get_gl_drawable (widget)
*)
fun gtk_widget_get_gl_drawable 
  {c1:cls | c1 <= GtkWidget}
  {l1:addr} (
  widget: !gobjref (c1, l1)
) : [c2:cls;l2:addr | c2 <= GdkGLDrawable] (
  minus (gobjref (c1, l1), gobjref (c2, l2)) | gobjref (c2, l2)
) = "mac#atsctrb_gtk_widget_get_gl_drawable"
// end of [gtk_widget_get_gl_drawable]

(* ****** ****** *)

(* end of [gtk.sats] *)
