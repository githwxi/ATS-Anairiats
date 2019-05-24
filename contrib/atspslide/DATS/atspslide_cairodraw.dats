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

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"
staload "contrib/cairo/SATS/cairo_extra.sats"

(* ****** ****** *)

staload "contrib/atspslide/SATS/atspslide.sats"

(* ****** ****** *)

staload
TM = "libc/SATS/time.sats"
stadef tm_struct = $TM.tm_struct
macdef time_get = $TM.time_get
macdef localtime_r = $TM.localtime_r

(* ****** ****** *)

staload M = "libc/SATS/math.sats"
macdef PI = $M.M_PI
macdef _2PI = 2 * PI
macdef _PI2 = PI / 2
macdef sin = $M.sin
macdef cos = $M.cos

(* ****** ****** *)

implement
cairodraw_clock01
  (cr, knd) = () where {
//
  var t = time_get ()
  var tm: tm_struct // unintialized
//
  val _ptr = localtime_r (t, tm)
  val () = assertloc (_ptr > null)
  prval () = opt_unsome {tm_struct} (tm)
//
  val ms = tm.tm_min * PI / 30
  val hs = tm.tm_hour * PI / 6 + ms / 12
  val ss = tm.tm_sec * PI / 30
//
  val (pf | ()) = cairo_save (cr)
  val () = cairo_translate (cr, 0.5, 0.5)
//
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_ROUND)
  val () = cairo_set_line_width (cr, 0.1)
//
  // draw a black clock outline
  val () = cairo_new_path (cr)
  val () = cairo_arc (cr, 0.0, 0.0, 0.4, 0.0, _2PI)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 0.1)
  val () = cairo_stroke (cr)
//
  // draw a green dot on the current second
  val () = if knd > 0 then {
    val () = cairo_arc
      (cr, 0.4 * sin(ss), 0.4 * ~cos(ss), 0.05, 0.0, _2PI)
    val () = cairo_set_source_rgba (cr, 0.0, 1.0, 0.0, 0.250)
    val () = cairo_fill (cr)
  } // end of [val]
//
  // draw the minutes indicator
  val () = cairo_move_to (cr, 0.0, 0.0)
  val () = cairo_line_to (cr, 0.4 * sin(ms), 0.4 * ~cos(ms))
  val () = cairo_set_source_rgba (cr, 0.2, 0.2, 1.0, 0.125)
  val () = cairo_stroke(cr)
//
  // draw the hours indicator
  val () = cairo_move_to (cr, 0.0, 0.0)
  val () = cairo_line_to (cr, 0.2 * sin(hs), 0.2 * ~cos(hs))
  val () = cairo_set_source_rgba (cr, 0.2, 0.2, 1.0, 0.125)
  val () = cairo_stroke (cr)
//
  val () = cairo_restore (pf | cr)
//
} // end of [cairodraw_clock01]

(* ****** ****** *)

local

stadef dbl = double
stadef cr (l:addr) = cairo_ref (l)

fn draw_hand {l:agz} (
  cr: !cr l, bot: dbl, top:dbl, len: dbl
) : void = let
  val () = cairo_move_to (cr, 0.0, bot/2)
  val () = cairo_line_to (cr, len, top/2)
  val () = cairo_line_to (cr, len, ~top/2)
  val () = cairo_line_to (cr, 0.0, ~bot/2)
  val () = cairo_close_path (cr)
in
  cairo_fill (cr)
end // end of [draw_hand]

val theLastSec = ref_make_elt<int> (~1)

fn draw_clock
  {l:agz} (
  cr: !cr l, knd: int
, h: natLt 24, m: natLt 60, s: natLt 60 // hour and minute
) : void = let
//
  val dim = 100.0 // please scale it!
  val rad = 0.375 * dim
//
  val h = (if h >= 12 then h - 12 else h): natLt 12
  val s_ang = s * (PI / 30) - _PI2
  // val m_ang = m * (PI / 30) + s * (PI / 1800) - _PI2
  val m_ang = m * (PI / 30) - _PI2
  val h_ang = h * (PI / 6) + m * (PI / 360) - _PI2
//
  val () = cairo_arc
    (cr, 0.0, 0.0, rad, 0.0, 2 * PI)
  val () = cairo_set_source_rgba (cr, 1.0, 1.0, 1.0, 0.0)
  val () = cairo_fill (cr)
  val () = cairo_arc
    (cr, 0.0, 0.0, rad, 0.0, 2 * PI)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 1.0, 0.125)
  val () = cairo_set_line_width (cr, 4.0)
  val () = cairo_stroke (cr)
//
  val rad1 = 0.90 * rad
  val () = cairo_arc (cr, ~rad1, ~rad1, rad1,  0.0, _PI2)
  val () = cairo_arc (cr, ~rad1,  rad1, rad1, ~_PI2,  0.)
  val () = cairo_arc (cr,  rad1,  rad1, rad1, ~PI, ~_PI2)
  val () = cairo_arc (cr,  rad1, ~rad1, rad1,  _PI2,  PI)
  val () = cairo_fill (cr)
//
  val h_l = 0.60 * rad
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 1.0, 0.250)
  val () = cairo_rotate (cr, h_ang)
  val () = draw_hand (cr, 3.0, 1.5, h_l)
  val () = cairo_restore (pf | cr)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 1.0, 0.250)
  val () = cairo_rotate (cr, h_ang+PI)
  val () = draw_hand (cr, 3.0, 1.5, h_l/4)
  val () = cairo_restore (pf | cr)
//
  val m_l = 0.85 * rad
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 1.0, 0.250)
  val () = cairo_rotate (cr, m_ang)
  val () = draw_hand (cr, 2.0, 1.0, m_l)
  val () = cairo_restore (pf | cr)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 1.0, 0.250)
  val () = cairo_rotate (cr, m_ang+PI)
  val () = draw_hand (cr, 2.0, 1.0, h_l/4)
  val () = cairo_restore (pf | cr)
//
val () = if knd > 0 then {
  val s_l = 0.85 * rad
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 1.0, 0.250)
  val () = cairo_rotate (cr, s_ang)
  val () = draw_hand (cr, 1.0, 0.5, m_l)
  val () = cairo_restore (pf | cr)
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 1.0, 0.250)
  val () = cairo_rotate (cr, s_ang+PI)
  val () = draw_hand (cr, 1.0, 0.5, h_l/4)
  val () = cairo_restore (pf | cr)
} // end of [val]
//
  val (pf | ()) = cairo_save (cr)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 0.125)
  val () = cairo_new_sub_path (cr)
  val () = cairo_arc (cr, 0.0, 0.0, 2.5, 0.0, 2 * PI)  
  val () = cairo_fill (cr)
  val () = cairo_restore (pf | cr)
in
  // nothing
end // end of [draw_clock]

in // in of [local]

implement
cairodraw_clock02
  (cr, knd) = () where {
//
  val w = (double_of)1
  val h = (double_of)1
  val mn = min (w, h)
  val xc = w / 2 and yc = h / 2
  val (pf0 | ()) = cairo_save (cr)
  val () = cairo_translate (cr, xc, yc)
  val alpha = mn / 100
  val () = cairo_scale (cr, alpha, alpha)
//
  var t = time_get ()
  var tm: tm_struct // unintialized
  val _ptr = localtime_r (t, tm)
  val () = assert_errmsg (_ptr > null, #LOCATION)
  prval () = opt_unsome {tm_struct} (tm)
  val hr = tm.tm_hour and mt = tm.tm_min and sd = tm.tm_sec
  val hr = int1_of_int (hr)
  val () = assert (0 <= hr && hr < 24)
  val mt = int1_of_int (mt)
  val () = assert (0 <= mt && mt < 60)
  val sd = int1_of_int (sd)
  val () = assert (0 <= sd && sd < 60)
  val () = draw_clock (cr, knd, hr, mt, sd)
//
  val () = cairo_restore (pf0 | cr)
//
} // end of [cairodraw_clock02]

end // end of [local]

(* ****** ****** *)

implement
cairodraw_circnum (cr, int) = let
  val (pf | ()) = cairo_save (cr)
  val () = cairo_translate (cr, 0.5, 0.5)
  val () = cairo_arc (cr, 0.0, 0.0, 0.5, 0.0, _2PI)
  val () = cairo_set_source_rgb (cr, 1.0, 1.0, 1.0)
  val () = cairo_fill (cr)
  val utf8 = sprintf ("%i", @(int))
  val () = cairo_set_source_rgb (cr, 1.0, 0.5, 0.0) // orange?
  val () = cairo_show_text_inbox (cr, 0.50, 0.50, $UN.castvwtp1 (utf8))
  val () = cairo_restore (pf | cr)
  val () = strptr_free (utf8)
in
  // nothing
end // end of [cairodraw_circnum]

(* ****** ****** *)

(* end of [atspslide_cairodraw.dats] *)
