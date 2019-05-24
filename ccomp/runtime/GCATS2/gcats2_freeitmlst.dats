(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
**
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
// Time: October, 2009

(* ****** ****** *)

// #include "gcats2_ats.hats"

(* ****** ****** *)

#define ATSOPT_NAMESPACE "gcats2_freeitmlst_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

(*
** this implementation is mostly for testing purpose
*)
implement
freeitmlst_length {l} (xs0) = n where {
  var xs = __cast (xs0) where {
    extern castfn __cast (xs0: !freeitmlst_vt l):<> freeitmlst_vt l
  }
  fun loop {l:addr}
    (xs: &freeitmlst_vt l >> freeitmlst_vt null, res: int):<!ntm> int =
    if freeitmlst_is_cons (xs) then let
      val (pf | x) = freeitmlst_uncons (xs)
      prval () = __leak (pf) where { extern prfun __leak {v:view} (pf: v): void }
    in
      loop (xs, res + 1)
    end else let
      prval () = addr_is_gtez {l} () in res // loop exits
    end // end of [if]
  // end of [loop]
  val n = $effmask_ntm (loop (xs, 0))
  val _(*null*) = freeitmlst_free_null (xs)
} // end of [freeitmlst_length]

(* ****** ****** *)

%{

ats_void_type
gcats2_fprint_freeitmlst
  (ats_ptr_type out, ats_ptr_type xs) {
  int i = 0 ;
  while (xs) {
    if  (i > 0) fprintf((FILE*)out, ", ") ;
    fprintf((FILE*)out, "%p", xs) ; i += 1 ; xs = *(ats_ptr_type*)xs ;
  } // end of [while]
  return ;
} // end of [gcats2_fprint_freeitmlst]

%} // end of [%{]

(* ****** ****** *)

(* end of [gcats2_freeitmlst.dats] *)
