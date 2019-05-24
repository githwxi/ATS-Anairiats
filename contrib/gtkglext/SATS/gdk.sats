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
#include "gtkglext/CATS/gdk.cats"
%} // end of [%{#]

(* ****** ****** *)

staload
GLIB = "contrib/glib/SATS/glib.sats"
stadef gint = $GLIB.gint
stadef gboolean = $GLIB.gboolean

(* ****** ****** *)

staload
GOBJ = "contrib/glib/SATS/glib-object.sats"
stadef GObject = $GOBJ.GObject // class constant
stadef gobjref = $GOBJ.gobjref // boxed viewtype

(* ****** ****** *)

classdec GdkGLConfig : GObject
viewtypedef GdkGLConfig_ref (l:addr) = gobjref (GdkGLConfig, l)
viewtypedef GdkGLConfig_ref0 = [l:addr] GdkGLConfig_ref (l)
viewtypedef GdkGLConfig_ref1 = [l:addr | l > null] GdkGLConfig_ref (l)

(* ****** ****** *)

classdec GdkGLContext : GObject
viewtypedef GdkGLContext_ref (l:addr) = gobjref (GdkGLContext, l)
viewtypedef GdkGLContext_ref0 = [l:addr] GdkGLContext_ref (l)
viewtypedef GdkGLContext_ref1 = [l:addr | l > null] GdkGLContext_ref (l)

(* ****** ****** *)

classdec GdkGLDrawable : GObject
viewtypedef GdkGLDrawable_ref (l:addr) = gobjref (GdkGLDrawable, l)
viewtypedef GdkGLDrawable_ref0 = [l:addr] GdkGLDrawable_ref (l)
viewtypedef GdkGLDrawable_ref1 = [l:addr | l > null] GdkGLDrawable_ref (l)

(* ****** ****** *)

classdec GdkGLWindow : GObject
viewtypedef GdkGLWindow_ref (l:addr) = gobjref (GdkGLWindow, l)
viewtypedef GdkGLWindow_ref0 = [l:addr] GdkGLWindow_ref (l)
viewtypedef GdkGLWindow_ref1 = [l:addr | l > null] GdkGLWindow_ref (l)

(* ****** ****** *)

abst@ype GdkGLConfigMode = uint // enum type
macdef GDK_GL_MODE_RGB = $extval (GdkGLConfigMode, "GDK_GL_MODE_RGB")
macdef GDK_GL_MODE_RGBA = $extval (GdkGLConfigMode, "GDK_GL_MODE_RGBA")
macdef GDK_GL_MODE_INDEX = $extval (GdkGLConfigMode, "GDK_GL_MODE_INDEX")
macdef GDK_GL_MODE_SINGLE = $extval (GdkGLConfigMode, "GDK_GL_MODE_SINGLE")
macdef GDK_GL_MODE_DOUBLE = $extval (GdkGLConfigMode, "GDK_GL_MODE_DOUBLE")
macdef GDK_GL_MODE_STEREO = $extval (GdkGLConfigMode, "GDK_GL_MODE_STEREO")
macdef GDK_GL_MODE_ALPHA = $extval (GdkGLConfigMode, "GDK_GL_MODE_ALPHA")
macdef GDK_GL_MODE_DEPTH = $extval (GdkGLConfigMode, "GDK_GL_MODE_DEPTH")
macdef GDK_GL_MODE_STENCIL = $extval (GdkGLConfigMode, "GDK_GL_MODE_STENCIL")
macdef GDK_GL_MODE_ACCUM = $extval (GdkGLConfigMode, "GDK_GL_MODE_ACCUM")
macdef GDK_GL_MODE_MULTISAMPLE = $extval (GdkGLConfigMode, "GDK_GL_MODE_MULTISAMPLE")

fun lor_GdkGLConfigMode_GdkGLConfigMode
  (x1: GdkGLConfigMode, x2: GdkGLConfigMode): GdkGLConfigMode = "atspre_lor_uint_uint"
overload lor with lor_GdkGLConfigMode_GdkGLConfigMode

fun gdk_gl_config_new_by_mode
  (mode: GdkGLConfigMode): GdkGLConfig_ref1 = "mac#atsctrb_gdk_gl_config_new_by_mode"
// end of [gdk_gl_config_new_by_mode]

(* ****** ****** *)


(*
GdkGLContext*
gdk_gl_context_new (
  GdkGLDrawable *gldrawable
, GdkGLContext *share_list, gboolean direct, int render_type
) ; // end of [gdk_gl_context_new]
*)

(* ****** ****** *)

(*
void gdk_gl_context_destroy (GdkGLContext *glcontext);
*)

fun gdk_gl_context_destroy (
  glcontext: GdkGLContext_ref1
) : void
  = "mac#atsctrb_gdk_gl_context_destroy"
// end of [gdk_gl_context_destroy]

(* ****** ****** *)

(*
gboolean
gdk_gl_context_copy (
  GdkGLContext *glcontext, GdkGLContext *src, unsigned long mask
) ; // end of [gdk_gl_context_copy]
*)

(* ****** ****** *)

(*
GdkGLDrawable*
gdk_gl_context_get_gl_drawable (GdkGLContext *glcontext);
*)
fun
gdk_gl_context_get_gl_drawable
  {c1:cls | c1 <= GdkGLContext}
  {l1:addr} (
  glcontext: !gobjref (c1, l1)
) : [c2:cls;l2:addr | c2 <= GdkGLDrawable] (
  minus (gobjref (c1, l1), gobjref (c2, l2)) | gobjref (c2, l2)
) = "mac#atsctrb_gdk_gl_context_get_gl_drawable"
// end of [gdk_gl_context_get_gl_drawable]

(* ****** ****** *)

(*
GdkGLConfig* gdk_gl_context_get_gl_config (GdkGLContext *glcontext);
*)

fun
gdk_gl_context_get_gl_config
  {c1:cls | c1 <= GdkGLContext}
  {l1:addr} (
  glcontext: !gobjref (c1, l1)
) : [c2:cls;l2:addr | c2 <= GdkGLConfig] (
  minus (gobjref (c1, l1), gobjref (c2, l2)) | gobjref (c2, l2)
) = "mac#atsctrb_gdk_gl_context_get_gl_config"
// end of [gdk_gl_context_get_gl_config]

(* ****** ****** *)

(*
GdkGLContext*
gdk_gl_context_get_share_list (GdkGLContext *glcontext);
*)
fun
gdk_gl_context_get_gl_share_list
  {c1:cls | c1 <= GdkGLContext}
  {l1:addr} (
  glcontext: !gobjref (c1, l1)
) : [c2:cls;l2:addr | c2 <= GdkGLContext] (
  minus (gobjref (c1, l1), gobjref (c2, l2)) | gobjref (c2, l2)
) = "mac#atsctrb_gdk_gl_context_get_gl_share_list"
// end of [gdk_gl_context_get_gl_share_list]

(* ****** ****** *)

(*
gboolean gdk_gl_context_is_direct (GdkGLContext *glcontext);
*)
fun
gdk_gl_context_is_direct
  {c:cls | c <= GdkGLContext}
  {l:addr} (
  glcontext: !gobjref (c, l)
) : gboolean
  = "mac#atsctrb_gdk_gl_context_is_direct"
// end of [gdk_gl_context_is_direct]

(* ****** ****** *)

(*
int gdk_gl_context_get_render_type (GdkGLContext *glcontext);
*)
fun
gdk_gl_context_get_render_type
  {c:cls | c <= GdkGLContext}
  {l:addr} (
  glcontext: !gobjref (c, l)
) : int
  = "mac#atsctrb_gdk_gl_context_get_render_type"
// end of [gdk_gl_context_get_render_type]

(* ****** ****** *)

(*
GdkGLContext* gdk_gl_context_get_current (void)
*)

(* ****** ****** *)

(*
gboolean
gdk_gl_drawable_make_current (GdkGLDrawable *gldrawable, GdkGLContext *glcontext);
*)

(* ****** ****** *)

(*
gboolean
gdk_gl_drawable_is_double_buffered (gldrawable) ;
*)
fun
gdk_gl_drawable_is_double_buffered
  {c:cls | c <= GdkGLDrawable}
  {l:addr} (
  glcontext: !gobjref (c, l)
) : gboolean
  = "mac#atsctrb_gdk_gl_drawable_is_double_buffered"
// end of [gdk_gl_drawable_is_double_buffered]

(*
void gdk_gl_drawable_swap_buffers (GdkGLDrawable *gldrawable);
*)
fun
gdk_gl_drawable_swap_buffers
  {c:cls | c <= GdkGLDrawable} {l:addr} (
  gldrawable: !gobjref (c, l)
) : void = "mac#atsctrb_gdk_gl_drawable_swap_buffers"

(* ****** ****** *)

(*
void        gdk_gl_drawable_wait_gl         (GdkGLDrawable *gldrawable);
void        gdk_gl_drawable_wait_gdk        (GdkGLDrawable *gldrawable);
*)

(* ****** ****** *)

absview gdkgl_begin_v (addr, bool)

(*
gboolean
gdk_gl_drawable_gl_begin (gldrawable, glcontext);
*)
fun
gdk_gl_drawable_gl_begin
  {c1,c2:cls | c1 <= GdkGLDrawable; c2 <= GdkGLContext}
  {l1,l2:addr} (
  gldrawable: !gobjref (c1, l1), glcontext: !gobjref (c2, l2)
) : [b:bool] (gdkgl_begin_v (l1, b) | bool (b))
  = "mac#atsctrb_gdk_gl_drawable_gl_begin"
// end of [gdk_gl_drawable_gl_begin]

(*
void gdk_gl_drawable_gl_begin (gldrawable);
*)
fun
gdk_gl_drawable_gl_end
  {c:cls | c <= GdkGLDrawable}
  {l:addr} (
  pf: gdkgl_begin_v (l, true) | gldrawable: !gobjref (c, l)
) : void = "mac#atsctrb_gdk_gl_drawable_gl_end"

prfun
gdkgl_begin_false_elim
  {l:addr} (pf: gdkgl_begin_v (l, false)): void
// end of [gdkgl_begin_false_elim]

(* ****** ****** *)

(*
void gdk_gl_drawable_get_size
  (GdkGLDrawable *gldrawable, gint *width, gint *height);
// end of [gdk_gl_drawable_get_size]
*)
fun
gdk_gl_drawable_get_size
  {c:cls | c <= GdkGLDrawable}
  {l:addr} (
  gldrawable: !gobjref (c, l), width: &gint >> gint, height: &gint? >> gint  
) : void = "mac#atsctrb_gdk_gl_drawable_get_size"

(* ****** ****** *)

(*
GdkGLConfig*
gdk_gl_drawable_get_gl_config  (GdkGLDrawable *gldrawable);
*)

(*
GdkGLDrawable* gdk_gl_drawable_get_current  (void);
*)

(* ****** ****** *)

(* end of [gdk.sats] *)
