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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [array.sats] starts!\n"
#endif // end of [VERBOSE_PRELUDE]

(* ****** ****** *)

exception ArraySubscriptException of ()

(* ****** ****** *)

fun{a:t@ype}
array_ptr_get_elt_at {n:int}
  {i:nat | i < n} (A: &(@[a][n]), i: size_t i):<> a
overload [] with array_ptr_get_elt_at

fun{a:t@ype}
array_ptr_set_elt_at {n:int}
  {i:nat | i < n} (A: &(@[a][n]), i: size_t i, x: a):<> void
overload [] with array_ptr_set_elt_at

fun{a:viewt@ype}
array_ptr_xch_elt_at {n:int}
  {i:nat | i < n} {l:addr} (A: &(@[a][n]), i: size_t i, x: &a):<> void
// end of [array_ptr_xch_elt_at]

(* ****** ****** *)

//
// these functions are present mostly for convenience as a programmer
// ofter uses values of the type int as array indices:
//

fun{a:t@ype}
array_ptr_get_elt_at__intsz
  {n:int} {i:nat | i < n} (A: &(@[a][n]), i: int i):<> a
overload [] with array_ptr_get_elt_at__intsz

fun{a:t@ype}
array_ptr_set_elt_at__intsz
  {n:int} {i:nat | i < n} (A: &(@[a][n]), i: int i, x:a):<> void
overload [] with array_ptr_set_elt_at__intsz

fun{a:viewt@ype}
array_ptr_xch_elt_at__intsz {n:int}
  {i:nat | i < n} {l:addr} (A: &(@[a][n]), i: int i, x: &a):<> void
// end of [array_ptr_xch_elt_at__intsz]

(* ****** ****** *)

(*

dataview
array_v (
  a:viewt@ype+, int, addr
) =
  | {n:int | n >= 0} {l:addr}
      array_v_cons (a, n+1, l) of (a @ l, array_v (a, n, l+sizeof a))
  | {l:addr} array_v_nil (a, 0, l)
// end of [array_v]

*)

viewdef array_v (a:viewt@ype, n:int, l: addr) = @[a][n] @ l

(* ****** ****** *)

praxi array_v_nil :
  {a:viewt@ype} {l:addr} () -<prf> array_v (a, 0, l)
praxi array_v_unnil :
  {a:viewt@ype} {l:addr} array_v (a, 0, l) -<prf> void

praxi array_v_cons :
  {a:viewt@ype} {n:nat} {l:addr}
  (a @ l, array_v (a, n, l+sizeof a)) -<prf> array_v (a, n+1, l)
praxi array_v_uncons :
  {a:viewt@ype} {n:int | n > 0} {l:addr}
  array_v (a, n, l) -<prf> (a @ l, array_v (a, n-1, l+sizeof a))

(* ****** ****** *)

prfun array_v_sing
  {a:viewt@ype} {l:addr} (pf: a @ l): array_v (a, 1, l)
prfun array_v_unsing
  {a:viewt@ype} {l:addr} (pf: array_v (a, 1, l)): a @ l

(* ****** ****** *)

praxi free_gc_viewt0ype_addr_trans
  {a1,a2:viewt@ype | sizeof a1 == sizeof a2}
  {n1,n2:int} {l:addr} {asz:int} (
  pf1_mul: MUL (n1, sizeof a1, asz)
, pf2_mul: MUL (n2, sizeof a2, asz) 
, pf_gc: !free_gc_v (a1, n1, l) >> free_gc_v (a2, n2, l)
) : void // end of [free_gc_viewt0ype_addr_trans]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_alloc {n:nat} (asz: size_t n)
  :<> [l:agz] (free_gc_v (a?, n, l), array_v (a?, n, l) | ptr l)
// end of [array_ptr_alloc]

(*
// implemented in C
*)
fun array_ptr_alloc_tsz
  {a:viewt@ype} {n:nat} (asz: size_t n, tsz: sizeof_t a):<>
    [l:agz] (free_gc_v (a?, n, l), array_v (a?, n, l) | ptr l)
  = "atspre_array_ptr_alloc_tsz"
// end of [array_ptr_alloc_tsz]

(* ****** ****** *)

(*
// implemented in C
*)
fun array_ptr_free
  {a:viewt@ype} {n:int} {l:addr} (
  pf_gc: free_gc_v (a?, n, l), pf_arr: array_v (a?, n, l) | p_arr: ptr l
) :<> void = "atspre_array_ptr_free"

(* ****** ****** *)

(*
** [array_ptr_allocfree] does not save much; if one does not want to deal with the
** view [free_gc_v] directly, then please use it.
*)

fun{a:viewt@ype}
array_ptr_allocfree {n:nat} (asz: size_t n):<>
    [l:agz] (array_v (a?, n, l) | ptr l, (array_v (a?, n, l) | ptr l) -<lin> void)
// end of [array_ptr_allocfree]

fun array_ptr_allocfree_tsz
  {a:viewt@ype} {n:nat} (asz: size_t n, tsz: sizeof_t a):<>
    [l:agz] (array_v (a?, n, l) | ptr l, (array_v (a?, n, l) | ptr l) -<lin> void)
// end of [array_ptr_allocfree_tsz]

(* ****** ****** *)

fun{a:t@ype}
array_ptr_initialize_elt {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: size_t n, ini: a):<> void
// end of [array_ptr_initialize_elt]

(*
// implemented in C
*)
fun array_ptr_initialize_elt_tsz {a:t@ype} {n:nat}
  (base: &(@[a?][n]) >> @[a][n], asz: size_t n, ini: &a, tsz: sizeof_t a):<> void
  = "atspre_array_ptr_initialize_elt_tsz"
// end of [array_ptr_initialize_elt_tsz]

(* ****** ****** *)

fun{a:t@ype}
array_ptr_initialize_lst {n:nat}
  (base: &(@[a?][n]) >> @[a][n], xs: list (a, n)):<> void
// end of [array_ptr_initialize_lst]

// the linear list is freed along the way
fun{a:viewt@ype} array_ptr_initialize_lst_vt {n:nat}
  (base: &(@[a?][n]) >> @[a][n], xs: list_vt (a, n)):<> void
// end of [array_ptr_initialize_lst_vt]

(* ****** ****** *)

(*
** HX: implemented in ATS (prelude/DATS/array.dats)
*)
fun array_ptr_initialize_funenv_tsz
  {a:viewt@ype}
  {v:view} {vt:viewtype}
  {n:nat} {f:eff} (
  pfv: !v
| base: &(@[a?][n]) >> @[a][n]
, asz: size_t n
, f: (!v | sizeLt n, &(a?) >> a, !vt) -<f> void
, tsz: sizeof_t a
, env: !vt
) :<f> void
  = "atspre_array_ptr_initialize_funenv_tsz"
// end of [fun]

fun{a:viewt@ype}
array_ptr_initialize_fun
 {n:nat} {f:eff} (
  base: &(@[a?][n]) >> @[a][n]
, asz: size_t n
, f: (sizeLt n, &(a?) >> a) -<fun,f> void
) :<f> void // end of [array_ptr_initialize_fun]

(* ****** ****** *)

(*
// implemented in ATS (prelude/DATS/array.dats)
*)
fun array_ptr_initialize_cloenv_tsz
  {a:viewt@ype} {v:view} {vt:viewtype} {n:nat} (
  pf: !v
| base: &(@[a?][n]) >> @[a][n]
, asz: size_t n
, f: &(!v | sizeLt n, &(a?) >> a, !vt) -<clo> void
, tsz: sizeof_t a
, env: !vt
) :<> void // end of [array_ptr_initialize_cloenv_tsz]

fun{a:viewt@ype}
array_ptr_initialize_clo
  {v:view} {n:nat} (
  pf: !v 
| base: &(@[a?][n]) >> @[a][n]
, asz: size_t n
, f: &(!v | sizeLt n, &(a?) >> a) -<clo> void
) :<> void // end of [array_ptr_initialize_clo]

(* ****** ****** *)

(*
// implemented in ATS (prelude/DATS/array.dats)
*)
fun array_ptr_clear_clo_tsz
  {a:viewt@ype} {v:view} {n:nat} (
  pf: !v
| base: &(@[a][n]) >> @[a?][n]
, asz: size_t n
, f: &(!v | &a >> a?) -<clo> void
, tsz: sizeof_t (a)
) :<> void // end of [array_ptr_clear_clo_tsz]

(* ****** ****** *)

prfun array_v_split {a:viewt@ype}
  {n:int} {i:nat | i <= n} {l:addr} {ofs:int} (
  pf_mul: MUL (i, sizeof a, ofs), pf_arr: array_v (a, n, l)
) :<prf> @(
  array_v (a, i, l), array_v (a, n-i, l+ofs)
) // end of [array_v_split]

(* ***** ***** *)

prfun array_v_unsplit {a:viewt@ype}
  {n1,n2:int} {l:addr} {ofs:int} (
  pf_mul: MUL (n1, sizeof a, ofs)
, pf1_arr: array_v (a, n1, l), pf2_arr: array_v (a, n2, l+ofs)
) :<prf> array_v (a, n1+n2, l)
// end of [array_v_unsplit]

(* ***** ***** *)

prfun array_v_extend :
  {a:viewt@ype} {n:nat} {l:addr} {ofs:int}
  (MUL (n, sizeof a, ofs), array_v (a, n, l), a @ l+ofs) -<prf> array_v (a, n+1, l)
// end of [array_v_extend]

prfun array_v_unextend : {a:viewt@ype}
  {n:int | n > 0} {l:addr} {ofs:int}
  (MUL (n, sizeof a, ofs), array_v (a, n, l)) -<prf> (array_v (a, n-1, l), a @ l+ofs-sizeof a)
// end of [array_v_unextend]

prfun array_v_takeout : {a:viewt@ype}
  {n:int} {i:nat | i < n} {l:addr} {ofs:int}
  (MUL (i, sizeof a, ofs), array_v (a, n, l)) -<prf> (a @ l+ofs, a @ l+ofs -<lin> array_v (a, n, l))
// end of [array_v_takeout]

prfun array_v_takeout2 : {a:viewt@ype}
  {n:int} {i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {l:addr} {ofs1,ofs2:int}
    (MUL (i1, sizeof a, ofs1), MUL (i2, sizeof a, ofs2), array_v (a, n, l)) -<prf>
    (a @ l+ofs1, a @ l+ofs2, (a @ l+ofs1, a @ l+ofs2) -<lin> array_v (a, n, l))
// end of [array_v_takeou2]

(* ***** ***** *)

prfun array_v_clear : // not really needed as [array_v] is covariant
  {a:t@ype} {n:nat} {l:addr} array_v (a, n, l) -<prf> array_v (a?, n, l)
// end of [array_v_clear]

(* ***** ***** *)

prfun array_v_group : {a:viewt@ype} {m,n:nat} {l:addr} {mn:int}
  (MUL (m, n, mn) | array_v (a, mn, l)) -<prf> array_v (@[a][n], m, l)
// end of [array_v_group]

prfun array_v_ungroup : {a:viewt@ype} {m,n:nat} {l:addr} {mn:int}
  (MUL (m, n, mn) | array_v (@[a][n], m, l)) -<prf> array_v (a, mn, l)
// end of [array_v_ungroup]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_split
  {n:int} {i:nat | i <= n} {l0:addr} (
  pf: array_v (a, n, l0) | base: ptr l0, offset: size_t i
) :<> [ofs:nat] (
  MUL (i, sizeof(a), ofs)
, array_v (a, i, l0), array_v (a, n-i, l0+ofs)
| ptr (l0+ofs)
) // end of [array_ptr_split]

(*
// implemented in C (prelude/CATS/array.cats)
*)
fun array_ptr_split_tsz
  {a:viewt@ype}
  {n:int} {i:nat | i <= n} {l0:addr} (
  pf: array_v (a, n, l0) | base: ptr l0, offset: size_t i, tsz: sizeof_t a
) :<> [ofs:nat] (
  MUL (i, sizeof(a), ofs)
, array_v (a, i, l0), array_v (a, n-i, l0+ofs)
| ptr (l0+ofs)
) = "atspre_array_ptr_split_tsz"
// end of [array_ptr_split_tsz]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_takeout
  {n:int} {i:nat | i < n} {l0:addr} (
  pf: array_v (a, n, l0) | base: ptr l0, offset: size_t i
) :<> [l:addr] (
  a @ l
, a @ l -<lin,prf> array_v (a, n, l0)
| ptr l
) // end of [array_ptr_takeout]

(*
// implemented in C (prelude/CATS/array.cats)
*)
fun array_ptr_takeout_tsz
  {a:viewt@ype}
  {n:int} {i:nat | i < n} {l0:addr} (
  pf: array_v (a, n, l0)
| base: ptr l0, offset: size_t i, tsz: sizeof_t a
) :<> [l:addr] (
  a @ l
, a @ l -<lin,prf> array_v (a, n, l0)
| ptr l
) = "atspre_array_ptr_takeout_tsz"
// end of [array_ptr_takeout_tsz]

(* ****** ****** *)

fun{a:viewt@ype}
array_ptr_takeout2 {n:int}
  {i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {l0:addr} (
  pf: array_v (a, n, l0)
| base: ptr l0
, off1: size_t i1, off2: size_t i2
) :<> [l1,l2:addr] (
  a @ l1
, a @ l2, (a @ l1, a @ l2) -<lin,prf> array_v (a, n, l0)
| ptr l1
, ptr l2
) // end of [array_ptr_takeout2]

(*
// implemented in ATS (prelude/DATS/array.dats)
*)
fun array_ptr_takeout2_tsz {a:viewt@ype}
  {n:int} {i1,i2:nat | i1 < n; i2 < n; i1 <> i2} {l0:addr} (
  pf: array_v (a, n, l0)
| base: ptr l0
, off1: size_t i1, off2: size_t i2
, tsz: sizeof_t a
) :<> [l1,l2:addr] (
  a @ l1
, a @ l2, (a @ l1, a @ l2) -<lin,prf> array_v (a, n, l0)
| ptr l1
, ptr l2
) // end of [array_ptr_takeout2_tsz]

(* ****** ****** *)

(*
// implemented in C (prelude/CATS/array.cats)
*)
fun array_ptr_copy_tsz {a:t@ype} {n:nat} (
  A: &(@[a][n]), B: &(@[a?][n]) >> @[a][n], n: size_t n
, tsz: sizeof_t a
) :<> void = "atspre_array_ptr_copy_tsz"
// end of [array_ptr_copy_tsz]

(*
// implemented in C (prelude/CATS/array.cats)
*)
fun array_ptr_move_tsz {a:viewt@ype} {n:nat} (
  A: &(@[a][n]) >> @[a?][n], B: &(@[a?][n]) >> @[a][n], n: size_t n
, tsz: sizeof_t a
) :<> void = "atspre_array_ptr_move_tsz"
// end of [array_ptr_move_tsz]

(*
// implemented in ATS (prelude/DATS/array.dats)
*)
fun{a:viewt@ype}
array_ptr_exch
  {n:int} {i1,i2:nat | i1 < n; i2 < n; i1 <> i2}
  (A: &(@[a][n]), i1: size_t i1, i2: size_t i2):<> void
// end of [array_ptr_exch]

(* ****** ****** *)
//
// HX: implemented in ATS (prelude/DATS/array.dats)
//
fun array_ptr_foreach_funenv_tsz
  {a:viewt@ype}
  {v:view} {vt:viewtype}
  {n:nat} {f:eff} (
  pfv: !v
| base: &(@[a][n])
, f: (!v | &a, !vt) -<fun,f> void
, asz: size_t n
, tsz: sizeof_t a
, env: !vt
) :<f> void
  = "atspre_array_ptr_foreach_funenv_tsz"
// end of [fun]

fun{a:viewt@ype}
array_ptr_foreach_fun
  {n:nat} {f:eff} (
  base: &(@[a][n]), f: (&a) -<fun,f> void, asz: size_t n
) :<f> void // end of [array_ptr_foreach_fun]

fun{a:viewt@ype}
array_ptr_foreach_clo
  {v:view} {n:nat} {f:eff} (
  pfv: !v
| base: &(@[a][n]), f: &(!v | &a) -<clo,f> void, asz: size_t n
) :<f> void // end of [array_ptr_foreach_clo]

(* ****** ****** *)

//
// HX: implemented in ATS (prelude/DATS/array.dats)
//
fun array_ptr_iforeach_funenv_tsz
  {a:viewt@ype}
  {v:view} {vt:viewtype}
  {n:nat} {f:eff} (
  pfv: !v
| base: &(@[a][n])
, f: (!v | sizeLt n, &a, !vt) -<fun,f> void
, asz: size_t n
, tsz: sizeof_t a
, env: !vt
) :<f> void
  = "atspre_array_ptr_iforeach_funenv_tsz"
// end of [fun]

fun{a:viewt@ype}
array_ptr_iforeach_fun
  {n:nat} {f:eff} (
  base: &(@[a][n])
, f: (sizeLt n, &a) -<fun,f> void
, asz: size_t n
) :<f> void // end of [array_ptr_iforeach_fun]

fun{a:viewt@ype}
array_ptr_iforeach_clo
  {v:view} {n:nat} {f:eff} (
  pfv: !v
| base: &(@[a][n])
, f: &(!v | sizeLt n, &a) -<clo,f> void
, asz: size_t n
) :<f> void // end of [array_ptr_iforeach_clo]

(* ****** ****** *)

(*
// moving an array of (linear) elements to form a list
*)
fun{a:t@ype}
array_ptr_to_list {n:nat}
  (base: &(@[a][n]) >> @[a?][n], asz: size_t n):<> list_vt (a, n)
// end of [array_ptr_to_list]

(* ****** ****** *)

(*
**
** persistent arrays
**
*)

(* ****** ****** *)

castfn array_make_view_ptr
  {a:viewt@ype} {n:nat} {l:addr}
  (pf: array_v (a, n, l) | p: ptr l):<> array (a, n)
// end of [array_make_view_ptr]

castfn array_get_view_ptr
  {a:viewt@ype} {n:nat}
  (A: array (a, n)):<> [l:addr] (vbox (array_v (a, n, l)) | ptr l)
// end of [array_get_view_ptr]

(* ****** ****** *)

fun array_make_arrpsz
  {a:viewt@ype} {n:nat} (psz: arrpsz (a, n)):<> array (a, n)
// end of [array_make_arrpsz]

(* ****** ****** *)

fun{a:t@ype} array_make_elt
  {n:nat} (asz: size_t n, elt: a):<> array (a, n)
// end of [array_make_elt]

fun{a:t@ype} array_make_lst {n:nat}
  (asz: size_t n, xs: list (a, n)):<> array (a, n)
// end of [array_make_lst]

fun{a:viewt@ype} array_make_lst_vt {n:nat}
  (asz: size_t n, xs: list_vt (a, n)):<> array (a, n)
// end of [array_make_lst_vt]

(* ****** ****** *)

(*
** template
*)
fun{a:viewt@ype}
  array_make_clo {v:view} {n:nat} (
    pf: !v
  | asz: size_t n
  , f: &(!v | sizeLt n, &(a?) >> a) -<clo> void
  ) :<> array (a, n)
// end of [array_make_clo_tsz]

(*
** function
*)
fun array_make_clo_tsz
  {a:viewt@ype} {v:view} {n:nat} (
  pf: !v
| asz: size_t n
, f: &(!v | sizeLt n, &(a?) >> a) -<clo> void
, tsz: sizeof_t a
) :<> array (a, n)
// end of [array_make_clo_tsz]

(* ****** ****** *)

(*
** template
*)
fun{a:viewt@ype}
array_make_cloref {n:nat} (
  asz: size_t n
, f: (sizeLt n, &(a?) >> a) -<cloref> void
) :<fun> array (a, n)
// end of [array_make_cloref_tsz]

(*
** function
*)
fun array_make_cloref_tsz
  {a:viewt@ype} {n:nat} (
  asz: size_t n
, f: (sizeLt n, &(a?) >> a) -<cloref> void
, tsz: sizeof_t a
) :<fun> array (a, n)
// end of [array_make_cloref_tsz]

(* ****** ****** *)

fun{a:t@ype} array_get_elt_at {n:int}
  {i:nat | i < n} (A: array (a, n), i: size_t i):<!ref> a
overload [] with array_get_elt_at

fun{a:t@ype} array_set_elt_at {n:int}
  {i:nat | i < n} (A: array (a, n), i: size_t i, x: a):<!ref> void
overload [] with array_set_elt_at

fun{a:viewt@ype} array_xch_elt_at {n:int}
  {i:nat | i < n} (A: array (a, n), i: size_t i, x: &a):<!ref> void
// end of [array_xch_elt_at]

(* ****** ****** *)

fun{a:t@ype} array_get_elt_at__intsz {n:int}
  {i:nat | i < n} (A: array (a, n), i: int i):<!ref> a
overload [] with array_get_elt_at__intsz

fun{a:t@ype} array_set_elt_at__intsz {n:nat}
  {i:nat | i < n} (A: array (a, n), i: int i, x: a):<!ref> void
overload [] with array_set_elt_at__intsz

fun{a:viewt@ype} array_xch_elt_at__intsz {n:nat}
  {i:nat | i < n} (A: array (a, n), i: int i, x: &a):<!ref> void
// end of [array_xch_elt_at__intsz]

(* ****** ****** *)

fun{a:viewt@ype} array_exch {n:nat}
  (A: array (a, n), i: sizeLt n, j: sizeLt n):<!ref> void
// end of [array_exch]

(* ****** ****** *)
//
// HX: these functions are just as easy to be implemented on the spot
//
(*
** implemented in ATS (prelude/DATS/array.dats)
*)
fun{a:viewt@ype}
array_foreach_funenv
  {v:view} {vt:viewtype} {n:nat} (
  pfv: !v
| A: array (a, n)
, f: (!v | &a, !vt) -<> void
, asz: size_t n
, env: !vt
) :<!ref> void // end of [array_foreach_funenv]

fun{a:viewt@ype}
array_foreach_fun {n:nat} (
  A: array (a, n), f: (&a) -<fun> void, asz: size_t n
) :<!ref> void // end of [array_foreach_fun]

fun{a:viewt@ype}
array_foreach_clo {v:view} {n:nat} (
  pfv: !v | A: array (a, n), f: &(!v | &a) -<clo> void, asz: size_t n
) :<!ref> void // end of [array_foreach_clo]

fun{a:viewt@ype}
array_foreach_cloref {n:nat} (
  A: array (a, n), f: (&a) -<cloref> void, asz: size_t n
) :<!ref> void // end of [array_foreach_cloref]

(* ****** ****** *)
//
// HX: these functions are just as easy to be implemented on the spot
//
(*
** HX: implemented in ATS (prelude/DATS/array.dats)
*)
fun{a:viewt@ype}
array_iforeach_funenv
  {v:view} {vt:viewtype} {n:nat} (
  pfv: !v
| A: array (a, n)
, f: (!v | sizeLt n, &a, !vt) -<> void
, asz: size_t n
, env: !vt
) :<!ref> void
// end of [array_iforeach_funenv]

fun{a:viewt@ype}
array_iforeach_fun {n:nat} (
  A: array (a, n), f: (sizeLt n, &a) -<fun> void, asz: size_t n
) :<!ref> void // end of [array_iforeach_fun]

fun{a:viewt@ype}
array_iforeach_clo {v:view} {n:nat} (
  pfv: !v | A: array (a, n), f: &(!v | sizeLt n, &a) -<clo> void, asz: size_t n
) :<!ref> void // end of [array_iforeach_clo]

fun{a:viewt@ype}
array_iforeach_cloref {n:nat} (
  A: array (a, n), f: (sizeLt n, &a) -<cloref> void, asz: size_t n
) :<!ref> void // end of [array_iforeach_cloref]

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [array.sats] finishes!\n"
#endif // end of [VERBOSE_PRELUDE]

(* end of [array.sats] *)
