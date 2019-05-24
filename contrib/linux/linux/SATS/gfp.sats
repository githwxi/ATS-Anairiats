(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
**
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "contrib/linux/linux/CATS/gfp.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for staloading at run-time

(* ****** ****** *)

abst@ype gfp_t = $extype"gfp_t"
castfn uint_of_gfp (x: gfp_t): uint
castfn gfp_of_uint (x: uint): gfp_t
macdef GFP_KERNEL = $extval (gfp_t, "GFP_KERNEL")
macdef GFP_ATOMIC = $extval (gfp_t, "GFP_ATOMIC")
macdef GFP_NOWAIT = $extval (gfp_t, "GFP_NOWAIT")
macdef GFP_NOIO = $extval (gfp_t, "GFP_NOIO")
macdef GFP_NOFS = $extval (gfp_t, "GFP_NOFS")
macdef GFP_IOFS = $extval (gfp_t, "GFP_IOFS")
macdef GFP_TEMPORARY = $extval (gfp_t, "GFP_TEMPORARY")
macdef GFP_USER = $extval (gfp_t, "GFP_USER")
macdef GFP_HIGHUSER = $extval (gfp_t, "GFP_HIGHUSER")

abst@ype disjgfp_t = $extype"gfp_t"
macdef __GFP_DMA = $extval (disjgfp_t, "__GFP_DMA")
macdef __GFP_HIGHMEM = $extval (disjgfp_t, "__GFP_HIGHMEM")
macdef __GFP_DMA32 = $extval (disjgfp_t, "__GFP_DMA32")
macdef __GFP_MOVABLE = $extval (disjgfp_t, "__GFP_MOVABLE")

(* ****** ****** *)

fun lor_gfp_disjgfp
  (f: gfp_t, df: disjgfp_t): gfp_t = "mac#atsctrb_linux_lor_gfp_disjgfp"
overload lor with lor_gfp_disjgfp

(* ****** ****** *)

(* end of [kernel.sats] *)
