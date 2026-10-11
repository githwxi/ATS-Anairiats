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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
**
** Bidirectional row-major matrices
** (matrices moving from left to right and vice versa)
** Contributed by Artyom Shalkhakov (artyom.shalkhakov AT gmail DOT com)
** Time: November, 2011
**
*)

(* ****** ****** *)
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

staload "libats/SATS/biarray.sats"

(* ****** ****** *)
//
// bidirectional row-major matrix
//
absview bimatrix_v (a:viewt@ype+, (*rows*)int, (*cols*)int, addr, addr)

(*
dataview bimatrix_v (
  a:vt0p, (*rows*)int, (*cols*)int, addr, addr
) =
  | {l1:addr}
    bimatrix_v_nil (a, 0, 0, l1, l1)
  | {m,n:nat} {l1,l2,l3:addr}
    bimatrix_v_cons (a, m+1, n, l1, l3) of (
      biarray_v (a, n, l1, l2), bimatrix_v (a, m, n, l2, l3)
    ) // end of [bimatrix_v]
*)

(* ****** ****** *)

prfun bimatrix_v_of_matrix_v
  {a:viewt@ype} {m,n:int} {l1:addr}
  (pf: matrix_v (a, m, n, l1)): [l2:addr] bimatrix_v (a, m, n, l1, l2)
// end of [bimatrix_v_of_matrix_v]

prfun matrix_v_of_bimatrix_v
  {a:viewt@ype} {m,n:int} {l1,l2:addr}
  (pf: bimatrix_v (a, m, n, l1, l2)): matrix_v (a, m, n, l1)
// end of [matrix_v_of_bimatrix_v]

(* ****** ****** *)

prfun bimatrix_v_offset
  {a:viewt@ype} {m,n:int} {l1,l2:addr}
  (pf: !bimatrix_v (a, m, n, l1, l2)): [mn:int] (MUL (m, n, mn), MUL (mn, sizeof(a), l2-l1))
// end of [bimatrix_v_offset]

(* ****** ****** *)

prfun bimatrix_v_nil
  {a:viewt@ype}
  {n:nat} {l:addr} (): bimatrix_v (a, 0, n, l, l)
// end of [bimatrix_v_nil]

prfun bimatrix_v_unnil
  {a:viewt@ype} {n:nat} {l1,l2:addr}
  (pf: bimatrix_v (a, 0, n, l1, l2)): [l1==l2] void
// end of [bimatrix_v_unnil]

(* ****** ****** *)

prfun bimatrix_v_sing
  {a:viewt@ype} {n:nat} {l1,l2:addr}
  (pf: biarray_v (a, n, l1, l2)): bimatrix_v (a, 1, n, l1, l2)
// end of [bimatrix_v_sing]

prfun bimatrix_v_unsing
  {a:viewt@ype} {n:nat} {l1,l2:addr}
  (pf: bimatrix_v (a, 1, n, l1, l2)): biarray_v (a, n, l1, l2)
// end of [bimatrix_v_unsing]

prfun bimatrix_v_cons
  {a:viewt@ype}
  {m,n:nat} {l1,l2,l3:addr} (
  pf1: biarray_v (a, n, l1, l2), pf2: bimatrix_v (a, m, n, l2, l3)
) : bimatrix_v (a, m+1, n, l1, l3)
// end of [bimatrix_v_cons]

(* ****** ****** *)

prfun bimatrix_v_uncons
  {a:viewt@ype}
  {m:pos;n:nat} {l1,l3:addr} (
  pf: bimatrix_v (a, m, n, l1, l3)
) : [l2:addr] (
  biarray_v (a, n, l1, l2), bimatrix_v (a, m-1, n, l2, l3)
) // end of [bimatrix_v_uncons]

prfun bimatrix_v_snoc
  {a:viewt@ype}
  {m,n:nat} {l1,l2,l3:addr} (
  pf1: bimatrix_v (a, m, n, l1, l2), pf2: biarray_v (a, n, l2, l3)
) : bimatrix_v (a, m+1, n, l1, l3)
// end of [bimatrix_v_snoc]

(* ****** ****** *)

prfun bimatrix_v_unsnoc
  {a:viewt@ype} {m,n:nat} {l1,l3:addr} (
  pf: bimatrix_v (a, m, n, l1, l3)
) : [l2:addr] (bimatrix_v (a, m-1, n, l1, l2), biarray_v (a, n, l2, l3))
// end of [bimatrix_v_unsnoc]

(* ****** ****** *)

(* end of [bimatrix.sats] *)
