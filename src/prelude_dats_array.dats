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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{^
#include "prelude/CATS/array.cats"
%}

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynamic loading

(* ****** ****** *)

(* array pointers *)

%{$

typedef unsigned char byte ;

ats_void_type
atspre_array_ptr_initialize_elt_tsz (
   ats_ptr_type A
 , ats_size_type asz 
 , ats_ptr_type ini
 , ats_size_type tsz
 )  {
  int i, itsz ; int left ; ats_ptr_type p ;
  if (asz == 0) return ;
  memcpy (A, ini, tsz) ;
  i = 1 ; itsz = tsz ; left = asz - i ;
  while (left > 0) {
    p = (ats_ptr_type)(((byte*)A) + itsz) ;
    if (left <= i) {
      memcpy (p, A, left * tsz) ; return ;
    } /* end of [if] */
    memcpy (p, A, itsz);
    i = i + i ; itsz = itsz + itsz ; left = asz - i ;
  } /* end of [while] */
  return ;
} /* end of [atspre_array_ptr_initialize_elt_tsz] */

%} // end of [%{$]

(* ****** ****** *)

(* persistent arrays *)

(* ****** ****** *)

assume
array_viewt0ype_int_type
  (a:viewt@ype, n:int) = [l:addr] @{
  data= ptr l, view= vbox (array_v (a, n, l))
} // end of [array_viewt0ype_int_type]

(*
viewtypedef // this one is declared in [prelude/basic_sta.sats]
arrayptrsize_viewt0ype_int_viewt0ype (a: viewt@ype, n:int) =
  [l:addr | l <> null] (free_gc_v (a?, n, l), @[a][n] @ l | ptr l, int n)
*)

implement
array_make_arrpsz
  {a}{n} (psz) = let
  prval () = free_gc_elim {a?} {n} (psz.0)
  val (pfbox | ()) = vbox_make_view_ptr (psz.1 | psz.2)
in
  @{ data= psz.2, view= pfbox }
end // end of [array]

implement array_get_view_ptr (A) = @(A.view | A.data)

(* ****** ****** *)

(* end of [prelude_dats_array.dats] *)
