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
** A functional concatenable deque implementation based on fingertrees
** Please see the JFP paper by Hinze and Paterson on fingertrees for more
** details on this interesting data structure
**
** Contributed by
**   Robbie Harwood (rharwood AT cs DOT bu DOT edu)
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Time: November, 2010
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
// HX: indexed by deque size
//
abstype
deque_t0ype_int_type (elt:t@ype+, n:int)
stadef deque = deque_t0ype_int_type

(* ****** ****** *)

fun fundeque_size
  {a:t@ype} {n:nat} (xt: deque (a, n)):<> int (n)
// end of [fundeque_size]

(* ****** ****** *)

fun{} fundeque_nil {a:t@ype} ():<> deque (a, 0)

fun{} fundeque_is_nil
  {a:t@ype} {n:nat} (xt: deque (a, n)): bool (n==0)
// end of [fundeque_is_nil]

(* ****** ****** *)

fun{a:t@ype}
fundeque_cons {n:nat}
  (x: a, xt: deque (a, n)):<> deque (a, n+1)
// end of [fingertree0_cons]

fun{a:t@ype}
fundeque_uncons {n:pos}
  (xt: deque (a, n), r: &a? >> a):<> deque (a, n-1)
// end of [fundeque_uncons]

(* ****** ****** *)

fun{a:t@ype}
fundeque_snoc {n:nat}
  (xt: deque (a, n), x: a):<> deque (a, n+1)
// end of [fingertree0_snoc]

fun{a:t@ype}
fundeque_unsnoc {n:pos}
  (xt: deque (a, n), r: &a? >> a):<> deque (a, n-1)
// end of [fundeque_unsnoc]

(* ****** ****** *)

fun fundeque_append {a:t@ype} {n1,n2:nat}
  (xt1: deque (a, n1), xt2: deque (a, n2)):<> deque (a, n1+n2)
// end of [fundeque_append]

(* ****** ****** *)

fun{a:t@ype}
fundeque_foreach_cloptr
  {n:nat}
  (xs: deque (a, n), f: !(a) -<cloptr> void):<> void
// end of [fundeque_foreach_cloptr]
fun{a:t@ype}
fundeque_foreach_vcloptr
  {v:view} {n:nat}
  (pf: !v | xs: deque (a, n), f: !(!v | a) -<cloptr> void):<> void
// end of [fundeque_foreach_vcloptr]

fun{a:t@ype}
fundeque_foreach_cloref {n:nat}
  (xs: deque (a, n), f: (a) -<cloref> void):<> void
// end of [fundeque_foreach_cloref]

(* ****** ****** *)

fun{a:t@ype}
fundeque_rforeach_cloptr
  {n:nat}
  (xs: deque (a, n), f: !(a) -<cloptr> void):<> void
// end of [fundeque_rforeach_cloptr]
fun{a:t@ype}
fundeque_rforeach_vcloptr
  {v:view} {n:nat}
  (pf: !v | xs: deque (a, n), f: !(!v | a) -<cloptr> void):<> void
// end of [fundeque_rforeach_vcloptr]

fun{a:t@ype}
fundeque_rforeach_cloref {n:nat}
  (xs: deque (a, n), f: (a) -<cloref> void):<> void
// end of [fundeque_rforeach_cloref]

(* ****** ****** *)

(* end of [fundeque_fingertree.sats] *)
