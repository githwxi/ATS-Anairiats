(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

absviewtype thunk_t
absviewtype thunkopt_t (int)
viewtypedef Thunkopt = [i:two] thunkopt_t (i)

(* ****** ****** *)

fun thunk_make (f: () -<lin,cloptr1> void): thunk_t
  = "atslib_thunk_make"

fun thunk_exec (x: thunk_t): void
  = "atslib_thunk_exec"

(* ****** ****** *)

fun thunkopt_none ():<> thunkopt_t (0)
  = "atslib_thunkopt_none"

fun thunkopt_some (_: thunk_t):<> thunkopt_t (1)
  = "atslib_thunkopt_some"

fun thunkopt_is_none {i:int} (_: !thunkopt_t i):<> bool (i==0)
  = "atslib_thunkopt_is_none"

fun thunkopt_is_some {i:int} (_: !thunkopt_t i):<> bool (i==1)
  = "atslib_thunkopt_is_some"

fun thunkopt_unnone (_: thunkopt_t 0): void
  = "atslib_thunkopt_unnone"

fun thunkopt_unsome (_: thunkopt_t 1): thunk_t
  = "atslib_thunkopt_unsome"

(* ****** ****** *)

(* end of [letpar.dats] *)
