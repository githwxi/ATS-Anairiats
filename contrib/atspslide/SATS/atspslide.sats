(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software, Inc.
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
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: October, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)
//
abstype slide_type
typedef slide = slide_type
//
fun slideopt_get_by_indx (indx: int): Option_vt (slide)
fun slideopt_get_by_name (name: string): Option_vt (slide)
//
(* ****** ****** *)
//
// atspslide_cairodraw
//
(* ****** ****** *)
(*
** HX-2011-10-01:
** A clock that may be used as a layover
** The dimension of the clock is 1.0 by 1.0
*)
(*
** HX:
** knd = 0: no second hand
** knd > 0: show second hand
*)
fun cairodraw_clock01 {l:agz} (cr: !cairo_ref l, knd: int): void

(* ****** ****** *)
(*
** HX-2012-01-25:
** A clock that may be used as a layover
** The dimension of the clock is 1.0 by 1.0
*)
(*
** HX:
** knd = 0: no second hand
** knd > 0: show second hand
*)
fun cairodraw_clock02 {l:agz} (cr: !cairo_ref l, knd: int): void

(* ****** ****** *)
(*
** HX-2011-10-01:
** A given number at the center of a circle
** The dimension of the enclosing square is 1.0 by 1.0
*)
fun cairodraw_circnum {l:agz} (cr: !cairo_ref l, int: int): void

(* ****** ****** *)

fun cairodraw_slide {l:agz} (cr: !cairo_ref l, x: slide): void

(* ****** ****** *)
//
// atspslide_glTexture 
//
(* ****** ****** *)

fun glTexture_make_cairo_ref {l:agz}
  (fmt: GLenum_format (4), cr: !cairo_ref (l)): GLtexture
// end of [glTexture_make_cairo]

(* ****** ****** *)
//
// HX:
// vdir=0/1:up/down
// the lower left corner of the rectangle (in the xy-plane)
// is at (0, 0, 0)
//
fun glTexture_mapout_rect
  {i:int} {d:two} (
  gltext: !GLtexture(i)
, tx0: double, ty0: double
, tx1: double, ty1: double
, wrect: double, hrect: double, vdir: int(d)
) : void // end of [glTexture_mapout_rect]

(* ****** ****** *)
//
// HX:
// vdir=0/1:up/down
// the lower left corner of the rectangle (in the xy-plane)
// is at (0, 0, 0)
//
fun glTexture_mapout_rect_all {i:int} {d:two} (
  gltext: !GLtexture(i), wrect: double, hrect: double, vdir: int(d)
) : void // end of [glTexture_mapout_rect]
//
// HX:
// front(1), right(2), back(3), left(4), top(5) and bottom(6)
// the front lower left corner of the rectanglular solid is at
// (0, 0, 0)
//
fun
glTexture_mapout_cube12
  {i1,i2:int} {d:two} (
  gltext1: !GLtexture(i1)
, gltext2: !GLtexture(i2)
, wrect: double, hrect: double, vdir: int(d)
) : void // end of [glTexture_mapout_cube12]

fun
glTexture_mapout_cube14
  {i1,i2:int} {d:two} (
  gltext1: !GLtexture(i1)
, gltext2: !GLtexture(i2)
, wrect: double, hrect: double, vdir: int(d)
) : void // end of [glTexture_mapout_cube14]

fun
glTexture_mapout_cube15
  {i1,i2:int} {d:two} (
  gltext1: !GLtexture(i1)
, gltext2: !GLtexture(i2)
, wrect: double, hrect: double, vdir: int(d)
) : void // end of [glTexture_mapout_cube15]

fun glTexture_mapout_cube16
  {i1,i2:int} {d:two} (
  gltext1: !GLtexture(i1)
, gltext2: !GLtexture(i2)
, wrect: double, hrect: double, vdir: int(d)
) : void // end of [glTexture_mapout_cube16]

(* ****** ****** *)
//
// HX-2011-10-12:
// vdir=0/1:up/down
// the cylinder is positioned vertically
// the front center of the cylinder is at (0, 0, 0)
// angle: goes from 0 to 2*PI
// if angle = 0, this is the same as glTexture_mapout_rect
// if angle = PI, then the front half of the cylinder is covered
// if angle = 2*PI, then the whole cylinder is covered
//
fun glTexture_mapout_cylinder_vert
  {i:int} {d:two} {n:pos} (
  gltext: !GLtexture(i)
, wtext: double, htext: double, angle: double, vdir: int(d), nslice: int(n)
) : void // end of [glTexture_mapout_cylinder_vert]
//
// HX:
// vdir=0/1:up/down
// the cylinder is positioned horizontally
// the front center of the cylinder is at (0, 0, 0)
// angle: goes from 0 to 2*PI
// if angle = 0, this is the same as glTexture_mapout_rect
// if angle = PI, then the front half of the cylinder is covered
// if angle = 2*PI, then the whole cylinder is covered
//
fun glTexture_mapout_cylinder_hori
  {i:int} {d:two} {n:pos} (
  gltext: !GLtexture(i)
, wtext: double, htext: double, angle: double, vdir: int(d), nslice: int(n)
) : void // end of [glTexture_mapout_cylinder_hori]

(* ****** ****** *)
//
// HX:
// vdir=0/1:up/down
// the sphere is positioned horizontally
// the front center of the sphere is at (0, 0, 0)
// angle: goes from 0 to 2*PI
// if angle = 0, this is the same as glTexture_mapout_rect
// if angle = PI, then the front half of the sphere is covered
// if angle = 2*PI, then the whole sphere is covered
//
fun glTexture_mapout_sphere
  {i:int} {d:two} {n:pos} (
  gltext: !GLtexture(i)
, wtext: double, htext: double, vdir: int(d), angle: double, nslice: int (n)
) : void // end of [glTexture_mapout_sphere]

(* ****** ****** *)

(* end of [atspslide.sats] *)
