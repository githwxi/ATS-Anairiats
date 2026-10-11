(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October, 2010
//
(* ****** ****** *)
//
// HX: these unsafe features must be used with caution!
//
(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

staload "prelude/SATS/unsafe.sats"

(* ****** ****** *)

implement{a}
ptr0_get (p) = x where
{
  val [l:addr] p = (ptr1_of_ptr)p
  prval
    (pf, fpf) = __assert () where
  {
    extern praxi __assert (): (a @ l, a? @ l -<lin,prf> void)
  } // end of [prval]
  val x = !p
  prval () = fpf (pf)
} // end of [ptr0_get]

implement{a}
ptr0_set (p, x) = () where
{
  val [l:addr] p = (ptr1_of_ptr)p
  prval
    (pf, fpf) = __assert () where
  {
    extern praxi __assert (): (a? @ l, a @ l -<lin,prf> void)
  } // end of [prval]
  val () = !p := x
  prval () = fpf (pf)
} // end of [ptr0_set]

(* ****** ****** *)

implement{a} ptr1_get (p) = ptr0_get<a> (p)
implement{a} ptr1_set (p, x) = ptr0_set<a> (p, x)

(* ****** ****** *)

implement{a} ptrget (p) = ptr0_get<a> (p)
implement{a} ptrset (p, x) = ptr0_set<a> (p, x)

(* ****** ****** *)

(* end of [unsafe.dats] *)
