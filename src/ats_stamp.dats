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
// Time: October 2007

(* ****** ****** *)

%{^
#include "ats_counter.cats" /* only needed for [ATS/Geizella] */
%} // end of [%{^]

(* ****** ****** *)

staload Cnt = "ats_counter.sats"

(* ****** ****** *)

staload "ats_stamp.sats"

(* ****** ****** *)

assume stamp_t = $Cnt.count_t

(* ****** ****** *)

implement
lt_stamp_stamp (s1, s2) = $Cnt.lt_count_count (s1, s2)
implement
lte_stamp_stamp (s1, s2) = $Cnt.lte_count_count (s1, s2)

implement
eq_stamp_stamp (s1, s2) = $Cnt.eq_count_count (s1, s2)
implement
neq_stamp_stamp (s1, s2) = $Cnt.neq_count_count (s1, s2)

implement
compare_stamp_stamp (s1, s2) = $Cnt.compare_count_count (s1, s2)

(* ****** ****** *)

implement fprint_stamp (pf | out, s) = $Cnt.fprint_count (pf | out, s)
implement print_stamp (s) = print_mac (fprint_stamp, s)
implement prerr_stamp (s) = prerr_mac (fprint_stamp, s)

(* ****** ****** *)

implement tostring_stamp (s) = $Cnt.tostring_count (s)

(* ****** ****** *)

local val counter = $Cnt.counter_make () in
implement s2rtdat_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement s2cst_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement s2var_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement s2Var_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement s2exp_struct_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement s2exp_union_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement d2con_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement d2cst_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement d2mac_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement d2var_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

(* ****** ****** *)

local val counter = $Cnt.counter_make () in
implement funlab_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement tmplab_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

local val counter = $Cnt.counter_make () in
implement tmpvar_stamp_make () = $Cnt.counter_getinc counter
end // end of [local]

(* ****** ****** *)

(* end of [ats_stamp.dats] *)
