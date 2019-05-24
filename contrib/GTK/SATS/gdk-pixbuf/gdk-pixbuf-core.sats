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
// Time: May, 2010
//
(* ****** ****** *)

abst@ype
GdkPixbufError = $extype "GdkPixbufError"
macdef GDK_PIXBUF_ERROR_CORRUPT_IMAGE =
  $extval (GdkPixbufError, "GDK_PIXBUF_ERROR_CORRUPT_IMAGE")
macdef GDK_PIXBUF_ERROR_INSUFFICIENT_MEMORY =
  $extval (GdkPixbufError, "GDK_PIXBUF_ERROR_INSUFFICIENT_MEMORY")
macdef GDK_PIXBUF_ERROR_BAD_OPTION =
  $extval (GdkPixbufError, "GDK_PIXBUF_ERROR_BAD_OPTION")
macdef GDK_PIXBUF_ERROR_UNKNOWN_TYPE =
  $extval (GdkPixbufError, "GDK_PIXBUF_ERROR_UNKNOWN_TYPE")
macdef GDK_PIXBUF_ERROR_UNSUPPORTED_OPERATION =
  $extval (GdkPixbufError, "GDK_PIXBUF_ERROR_UNSUPPORTED_OPERATION")
macdef GDK_PIXBUF_ERROR_FAILED =
  $extval (GdkPixbufError, "GDK_PIXBUF_ERROR_FAILED")

(* ****** ****** *)

(*
fun gdk_pixbuf_error_quark
  (): GQuark = "#atsctrb_gdk_pixbuf_error_quark"
// end of [gdk_pixbuf_error_quark]
*)

(* ****** ****** *)

abst@ype
GdkPixbufAlphaMode = $extype "GdkPixbufAlphaMode"
macdef GDK_PIXBUF_ALPHA_BILEVEL =
  $extval (GdkPixbufAlphaMode, "GDK_PIXBUF_ALPHA_BILEVEL")
macdef GDK_PIXBUF_ALPHA_FULL =
  $extval (GdkPixbufAlphaMode, "GDK_PIXBUF_ALPHA_FULL")

(* ****** ****** *)

abst@ype GdkColorspace = $extype "GdkColorspace"
macdef GDK_COLORSPACE_RGB = $extval (GdkColorspace, "GDK_COLORSPACE_RGB")

(* ****** ****** *)

(*
GdkColorspace gdk_pixbuf_get_colorspace      (const GdkPixbuf *pixbuf);
int           gdk_pixbuf_get_n_channels      (const GdkPixbuf *pixbuf);
gboolean      gdk_pixbuf_get_has_alpha       (const GdkPixbuf *pixbuf);
int           gdk_pixbuf_get_bits_per_sample (const GdkPixbuf *pixbuf);
guchar       *gdk_pixbuf_get_pixels          (const GdkPixbuf *pixbuf);
int           gdk_pixbuf_get_width           (const GdkPixbuf *pixbuf);
int           gdk_pixbuf_get_height          (const GdkPixbuf *pixbuf);
int           gdk_pixbuf_get_rowstride       (const GdkPixbuf *pixbuf);
*)

fun gdk_pixbuf_get_colorspace
  {c:cls | c <= GdkPixbuf}
  {l:agz} (
  pixbuf: !gobjref (c, l)
) : GdkColorspace
  = "mac#atsctrb_gdk_pixbuf_get_colorspace"
// end of [gdk_pixbuf_get_colorspace]

fun gdk_pixbuf_get_n_channels
  {c:cls | c <= GdkPixbuf} {l:agz} (pixbuf: !gobjref (c, l)): int
  = "mac#atsctrb_gdk_pixbuf_get_n_channels"
// end of [gdk_pixbuf_get_n_channels]

fun gdk_pixbuf_get_has_alpha
  {c:cls | c <= GdkPixbuf} {l:agz} (pixbuf: !gobjref (c, l)): gboolean
  = "mac#atsctrb_gdk_pixbuf_get_has_alpha"
// end of [gdk_pixbuf_get_has_alpha]

fun gdk_pixbuf_get_bits_per_sample
  {c:cls | c <= GdkPixbuf} {l:agz} (pixbuf: !gobjref (c, l)): int
  = "mac#atsctrb_gdk_pixbuf_get_bits_per_sample"
// end of [gdk_pixbuf_get_bits_per_sample]

fun gdk_pixbuf_get_pixels
  {c:cls | c <= GdkPixbuf}
  {l:agz} (
  pixbuf: !gobjref (c, l)
) : gpointer // guchar*
  = "mac#atsctrb_gdk_pixbuf_get_pixels"
// end of [gdk_pixbuf_get_pixels]

fun gdk_pixbuf_get_width
  {c:cls | c <= GdkPixbuf} {l:agz} (pixbuf: !gobjref (c, l)): int
  = "mac#atsctrb_gdk_pixbuf_get_width"
// end of [gdk_pixbuf_get_width]

fun gdk_pixbuf_get_height
  {c:cls | c <= GdkPixbuf} {l:agz} (pixbuf: !gobjref (c, l)): int
  = "mac#atsctrb_gdk_pixbuf_get_height"
// end of [gdk_pixbuf_get_height]

fun gdk_pixbuf_get_rowstride
  {c:cls | c <= GdkPixbuf} {l:agz} (pixbuf: !gobjref (c, l)): int
  = "mac#atsctrb_gdk_pixbuf_get_rowstride"
// end of [gdk_pixbuf_get_rowstride]

(* ****** ****** *)

(* end of [gdk-pixbuf-core.sats] *)
