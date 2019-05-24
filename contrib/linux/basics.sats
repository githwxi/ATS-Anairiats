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
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)
// Start Time: February, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

propdef ftakeout
  (v1:view, v2:view) = v1 -<prf> (v2, v2 -<lin,prf> v1)
// end of [ftakeout]

(* ****** ****** *)

(*
** HX-2011-02-20:
** a pointer is in kernel space by default
*)
abstype uptr (l:addr) // user space pointers

(* ****** ****** *)

absview kfree_addr_view (l:addr)
stadef kfree_v = kfree_addr_view

absview kfree_viewt0ype_addr_view  (a:viewt@ype+, l:addr)
stadef kfree_v = kfree_viewt0ype_addr_view

absview kfree_viewt0ype_int_addr_view  (a:viewt@ype+, n:int, l:addr)
stadef kfree_v = kfree_viewt0ype_int_addr_view
viewdef kfreebyte_v (n:int, l:addr) = kfree_v (byte, n, l)

(* ****** ****** *)

(* end of [basics.sats] *)
