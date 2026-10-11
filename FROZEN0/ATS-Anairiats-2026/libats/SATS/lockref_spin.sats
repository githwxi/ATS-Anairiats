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
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

%{#
#include "libats/CATS/lockref_spin.cats"
%} // end of [%{#]

(* ****** ****** *)

abstype
lock_view_type
  (v:view, l:addr)
stadef lock = lock_view_type
typedef lock0 (v:view) = [l:addr] lock (v, l)
typedef lock1 (v:view) = [l:addr | l > null] lock (v, l)

(* ****** ****** *)

castfn ptr_of_lock
  {v:view} {l:addr} (x: lock (v, l)):<> ptr (l)
// end of [ptr_of_lock]

(* ****** ****** *)

fun lockref_create_locked
  {v:view} (
  pshared: int
) : lock0 (v)
  = "atslib_lockref_create_locked"
// end of [lockref_create_locked]

fun lockref_create_unlocked
  {v:view} (
  pf: !v >> option_v (v, l==null) | pshared: int
) : #[l:addr] lock (v, l)
  = "atslib_lockref_create_unlocked"
// end of [lockref_create_unlocked]

(* ****** ****** *)

fun lockref_acquire
  {v:view} {l:agz} (x: lock (v, l)): (v | void)
  = "mac#atslib_lockref_acquire"
// end of [lockref_acquire]

fun lockref_acquire_try
  {v:view} {l:agz}
  (x: lock (v, l)): [i:nat] (option_v (v, i==0) | int i)
  = "mac#atslib_lockref_acquire_try"
// end of [lockref_acquire_try]

fun lockref_release
  {v:view} {l:agz} (pf: v | x: lock (v, l)): void
  = "mac#atslib_lockref_release"
// end of [lockref_release]

(* ****** ****** *)

(* end of [lockref_spin.sats] *)
