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
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

(*
**
** A functional random-access list implementation based on nested datatypes
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: April, 2010 // based on a version done in November, 2008
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)
//
// HX: indexed by list length
//
abstype ralist_t0ype_int_type (a:t@ype+, n:int)
stadef ralist = ralist_t0ype_int_type

(* ****** ****** *)

fun{} funralist_make_nil {a:t@ype} ():<> ralist (a, 0)

(* ****** ****** *)

fun{a:t@ype} funralist_length {n:nat} (xs: ralist (a, n)): int n

(* ****** ****** *)

fun{a:t@ype}
funralist_cons {n:nat} (x: a, xs: ralist (a, n)):<> ralist (a, n+1)
// end of [funralist_cons]

fun{a:t@ype}
funralist_uncons {n:pos} (xs: ralist (a, n), x: &a? >> a):<> ralist (a, n-1)
// end of [funralist_uncons]

(* ****** ****** *)

fun{a:t@ype} funralist_head {n:pos} (xs: ralist (a, n)):<> a
fun{a:t@ype} funralist_tail {n:pos} (xs: ralist (a, n)):<> ralist (a, n-1)

(* ****** ****** *)

fun{a:t@ype}
funralist_lookup {n:nat} (xs: ralist (a, n), i: natLt n):<> a
// end of [funralist_lookup]

fun{a:t@ype}
funralist_update {n:nat} (xs: ralist (a, n), i: natLt n, x: a):<> ralist (a, n)
// end of [funralist_update]

(* ****** ****** *)

fun{a:t@ype}
funralist_foreach_vclo {v:view} {n:nat} {f:eff}
  (pf: !v | xs: ralist (a, n), f: &(!v | a) -<clo,f> void):<f> void
// end of [funralist_foreach_vclo]

fun{a:t@ype}
funralist_foreach_cloptr {n:nat} {f:eff}
  (xs: ralist (a, n), f: !(a) -<cloptr,f> void):<f> void
// end of [funralist_foreach_vcloptr]
fun{a:t@ype}
funralist_foreach_vcloptr {v:view} {n:nat} {f:eff}
  (pf: !v | xs: ralist (a, n), f: !(!v | a) -<cloptr,f> void):<f> void
// end of [funralist_foreach_vcloptr]

fun{a:t@ype}
funralist_foreach_cloref {n:nat} {f:eff}
  (xs: ralist (a, n), f: (a) -<cloref,f> void):<f> void
// end of [funralist_foreach_cloref]

(* ****** ****** *)

(* end of [funralist_nested.sats] *)
