(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
// Time: July 2007

(* ****** ****** *)

(* ats_counter: counter implementation *)

(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload "ats_counter.sats"

(* ****** ****** *)

implement lt_count_count (cnt1, cnt2) = compare (cnt1, cnt2) < 0
implement lte_count_count (cnt1, cnt2) = compare (cnt1, cnt2) <= 0
implement gt_count_count (cnt1, cnt2) = compare (cnt1, cnt2) > 0
implement gte_count_count (cnt1, cnt2) = compare (cnt1, cnt2) >= 0
implement eq_count_count (cnt1, cnt2) = compare (cnt1, cnt2) = 0
implement neq_count_count (cnt1, cnt2) = compare (cnt1, cnt2) <> 0

(* ****** ****** *)

implement print_count (cnt) = print_mac (fprint_count, cnt)
implement prerr_count (cnt) = prerr_mac (fprint_count, cnt)

(* ****** ****** *)

(* end of [ats_counter.dats] *)
