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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [matrix.sats] starts!\n"
#endif // end of [VERBOSE_PRELUDE]

(* ****** ****** *)

absview matrix_v (a:viewt@ype, m:int, n:int, l:addr)

prfun array_v_of_matrix_v {a:viewt@ype} {m,n:int} {l:addr}
  (pf_mat: matrix_v (a, m, n, l)):<> [mn:nat] (MUL (m, n, mn), array_v (a, mn, l))

prfun matrix_v_of_array_v {a:viewt@ype} {m,n:nat} {mn:int} {l:addr}
  (pf_mul: MUL (m, n, mn), pf_arr: array_v (a, mn, l)):<> matrix_v (a, m, n, l)

(* ****** ****** *)

exception MatrixSubscriptException of ()

(* ****** ****** *)

fun matrix_ptr_takeout_tsz {a:viewt@ype}
  {m,n:int} {i,j:nat | i < m; j < n} {l0:addr} (
    pf_mat: matrix_v (a, m, n, l0)
  | base: ptr l0, i: size_t i, n: size_t n, j: size_t j, tsz: sizeof_t a
  ) :<> [l:addr] (
    a @ l
  , a @ l -<lin,prf> matrix_v (a, m, n, l0)
  | ptr l
  ) // end of [matrix_ptr_takeout_tsz]
(* end of [matrix_ptr_takeout_tsz] *)

(* ****** ****** *)

(*
**
** persistent matrices
**
*)

(* ****** ****** *)

fun matrix_make_arrpsz
  {a:viewt@ype} {m,n:nat}
  (m: size_t m, n: size_t n, psz: arrpsz (a, m*n))
  :<> matrix (a, m, n)
  = "atspre_matrix_make_arrpsz__main"
// end of [matrix_make_arrpsz]

(* ****** ****** *)
//
// HX: implemented in [prelude/DATS/matrix.dats]
//
fun matrix_make_arrpsz__main
  {a:viewt@ype}{m,n:nat}{mn:int} (
  pf: MUL (m, n, mn) | m: size_t m, n: size_t n, psz: arrpsz (a, mn)
) :<> matrix (a, m, n) = "atspre_matrix_make_arrpsz__main"
// end of [matrix_make_arrpsz__main]

(* ****** ****** *)

fun{a:t@ype} matrix_make_elt {m,n:pos}
  (row: size_t m, col: size_t n, elt: a):<> matrix (a, m, n)

(* ****** ****** *)

fun matrix_make_fun_tsz__main
  {a:viewt@ype} {v:view} {vt:viewtype} {m,n:pos} (
    pf: !v
  | row: size_t m, col: size_t n
  , f: (!v | sizeLt m, sizeLt n, &(a?) >> a, !vt) -<> void
  , tsz: sizeof_t a
  , env: !vt
  ) :<> matrix (a, m, n)

fun matrix_make_fun_tsz
  {a:viewt@ype} {v:view} {m,n:pos} (
    pf: !v
  | row: size_t m, col: size_t n
  , f: (!v | sizeLt m, sizeLt n, &(a?) >> a) -<fun> void
  , tsz: sizeof_t a
  ) :<> matrix (a, m, n)

fun matrix_make_clo_tsz
  {a:viewt@ype} {v:view} {m,n:pos} (
    pf: !v
  | row: size_t m, col: size_t n
  , f: &(!v | sizeLt m, sizeLt n, &(a?) >> a) -<clo> void
  , tsz: sizeof_t a
  ) :<> matrix (a, m, n)

(* ****** ****** *)

fun{a:t@ype} matrix_get_elt_at {m,n:int} {i,j:nat | i < m; j < n}
  (A: matrix (a, m, n), i: size_t i, n: size_t n, j: size_t j):<!ref> a
fun{a:t@ype} matrix_set_elt_at {m,n:int} {i,j:nat | i < m; j < n}
  (A: matrix (a, m, n), i: size_t i, n: size_t n, j: size_t j, x: a):<!ref> void
overload [] with matrix_get_elt_at
overload [] with matrix_set_elt_at

(* ****** ****** *)

fun{a:t@ype} matrix_get_elt_at__intsz {m,n:int} {i,j:nat | i < m; j < n}
  (A: matrix (a, m, n), i: int i, n: int n, j: int j):<!ref> a
fun{a:t@ype} matrix_set_elt_at__intsz {m,n:int} {i,j:nat | i < m; j < n}
  (A: matrix (a, m, n), i: int i, n: int n, j: int j, x: a):<!ref> void

overload [] with matrix_get_elt_at__intsz
overload [] with matrix_set_elt_at__intsz

(* ****** ****** *)

//
// these functions are just as easy to be implemented on the spot (HX)
//

(*
// implemented in ATS (prelude/DATS/matrix.dats)
*)
fun{a:viewt@ype}
matrix_foreach_fun__main
  {v:view} {vt:viewtype} {m,n:nat} (
    pf: !v
  | M: matrix (a, m, n)
  , f: (!v | &a, !vt) -<fun> void, m: size_t m, n: size_t n
  , env: !vt
  ) :<!ref> void
// end of [matrix_foreach_fun__main]

fun{a:viewt@ype}
matrix_foreach_fun {v:view} {m,n:nat} (
    pf: !v
  | M: matrix (a, m, n)
  , f: (!v | &a) -<fun> void, m: size_t m, n: size_t n
  ) :<!ref> void

fun{a:viewt@ype}
matrix_foreach_clo {v:view} {m,n:nat} (
    pf: !v
  | M: matrix (a, m, n)
  , f: &(!v | &a) -<clo> void, m: size_t m, n: size_t n
  ) :<!ref> void

fun{a:viewt@ype}
matrix_foreach_cloref {m,n:nat} (
    M: matrix (a, m, n), f: (&a) -<cloref> void, m: size_t m, n: size_t n
  ) :<!ref> void

(* ****** ****** *)

//
// these functions are just as easy to be implemented on the spot (HX)
//

(*
// implemented in ATS (prelude/DATS/matrix.dats)
*)
fun{a:viewt@ype}
matrix_iforeach_fun__main
  {v:view} {vt:viewtype} {m,n:nat} (
    pf: !v
  | M: matrix (a, m, n)
  , f: (!v | sizeLt m, sizeLt n, &a, !vt) -<fun> void, m: size_t m, n: size_t n
  , env: !vt
  ) :<!ref> void

fun{a:viewt@ype}
matrix_iforeach_fun {v:view} {m,n:nat} (
    pf: !v
  | M: matrix (a, m, n)
  , f: (!v | sizeLt m, sizeLt n, &a) -<fun> void, m: size_t m, n: size_t n
  ) :<!ref> void

fun{a:viewt@ype}
matrix_iforeach_clo {v:view} {m,n:nat} (
    pf: !v
  | M: matrix (a, m, n)
  , f: &(!v | sizeLt m, sizeLt n, &a) -<clo> void, m: size_t m, n: size_t n
  ) :<!ref> void

fun{a:viewt@ype}
matrix_iforeach_cloref {m,n:nat} (
    M: matrix (a, m, n)
  , f: (sizeLt m, sizeLt n, &a) -<cloref1> void, m: size_t m, n: size_t n
  ) :<fun1> void

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [matrix.sats] finishes!\n"
#endif // end of [VERBOSE_PRELUDE]

(* end of [matrix.sats] *)
