(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
#print "Loading [list_vt.sats] starts!\n"
#endif // end of [VERBOSE_PRELUDE]

(* ****** ****** *)

%{#
#include "prelude/CATS/list_vt.cats"
%} // end of [%{#]

(* ****** ****** *)

sortdef t0p = t@ype
sortdef vt0p = viewt@ype

(* ****** ****** *)

(*
// this is defined in [basic_sta.sats]
dataviewtype // viewt@ype+: covariant
list_viewt0ype_int_viewtype (a:viewt@ype+, int) =
  | {n:int | n >= 0}
    list_vt_cons (a, n+1) of (a, list_viewt0ype_int_viewtype (a, n))
  | list_vt_nil (a, 0)
// end of [list_viewt0ype_int_viewtype]
stadef list_vt = list_viewt0ype_int_viewtype
viewtypedef List_vt (a:viewt@ype) = [n:int | n >=0] list_vt (a, n)
*)

(* ****** ****** *)

macdef list_vt_sing (x) =
  list_vt_cons (,(x), list_vt_nil ())
macdef list_vt_pair (x1, x2) =
  list_vt_cons (,(x1), list_vt_cons (,(x2), list_vt_nil))

(* ****** ****** *)

prfun list_vt_length_is_nonnegative
  {a:vt0p} {n:int} (xs: !list_vt (a, n)): [n>=0] void
// end of [list_vt_length_is_nonnegative]

(* ****** ****** *)

fun{} list_vt_is_nil
  {a:vt0p} {n:int} (xs: !list_vt (a, n)):<> bool (n==0)
fun{} list_vt_is_cons
  {a:vt0p} {n:int} (xs: !list_vt (a, n)):<> bool (n > 0)

(* ****** ****** *)

fun{a:vt0p}
list_vt_make_array {n:int}
  (A: &(@[a][n]) >> @[a?!][n], n: size_t n):<> list_vt (a, n)
// end of [list_vt_make_array]

(* ****** ****** *)

fun{a:vt0p}
list_vt_of_arrpsz
  {n:int} (psz: arrpsz (a, n)):<> list_vt (a, n)
// end of [list_vt_of_arrpsz]

(* ****** ****** *)

fun{a:t0p}
list_vt_copy {n:int} (xs: !list_vt (a, n)):<> list_vt (a, n)

(* ****** ****** *)

fun{a:t0p}
list_vt_free (xs: List_vt a):<> void

fun{a:vt0p}
list_vt_free_fun (
  xs: List_vt a, f: (&a >> a?) -<fun> void
) :<> void // end of [list_vt_free_fun]

(* ****** ****** *)
//
// HX: this one is more general than [list_length] as [a] can be linear
//
fun{a:vt0p}
list_vt_length {n:int} (xs: !list_vt (a, n)):<> int n

(* ****** ****** *)

fun{a:t0p}
list_vt_make_elt {n:nat} (x: a, n: int n):<> list_vt (a, n)

(* ****** ****** *)

fun{a:vt0p}
list_vt_extend {n:int}
  (xs: list_vt (a, n), x: a):<> list_vt (a, n+1)
// end of [list_vt_extend]

(* ****** ****** *)

fun{a:vt0p}
list_vt_append {m,n:int}
  (xs: list_vt (a, m), ys: list_vt (a, n)):<> list_vt (a, m+n)
// end of [list_vt_append]

(* ****** ****** *)

fun{a:vt0p}
list_vt_split_at {n:int} {i:nat | i <= n}
  (xs: &list_vt (a, n) >> list_vt (a, n-i), i: int i):<> list_vt (a, i)
// end of [list_vt_split_at]

(* ****** ****** *)

fun{a:vt0p}
list_vt_reverse {n:int} (xs: list_vt (a, n)):<> list_vt (a, n)
// end of [list_vt_reverse]

fun{a:vt0p}
list_vt_reverse_append {m,n:int}
  (xs: list_vt (a, m), ys: list_vt (a, n)):<> list_vt (a, m+n)
// end of [list_vt_reverse_append]

(* ****** ****** *)

fun{a:vt0p}
list_vt_concat (xss: List_vt (List_vt (a))):<> List_vt (a)

(* ****** ****** *)

fun{a:vt0p}
list_vt_tabulate_funenv
  {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | f: (!v | natLt n, !vt) -<f> a, n: int n, env: !vt)
  :<f> list_vt (a, n)
// end of [list_vt_tabulate_funenv]

fun{a:vt0p}
list_vt_tabulate_fun {n:nat} {f:eff}
  (f: natLt n -<f> a, n: int n):<f> list_vt (a, n)
// end of [list_vt_tabulate_fun]

fun{a:vt0p}
list_vt_tabulate_vclo {v:view} {n:nat} {f:eff}
  (pf: !v | f: &(!v | natLt n) -<clo,f> a, n: int n):<f> list_vt (a, n)
// end of [list_vt_tabulate_vclo]

fun{a:vt0p}
list_vt_tabulate_cloptr {n:nat} {f:eff}
  (f: !(natLt n) -<cloptr,f> a, n: int n):<f> list_vt (a, n)
// end of [list_vt_tabulate_cloptr]
fun{a:vt0p}
list_vt_tabulate_vcloptr {v:view} {n:nat} {f:eff}
  (pf: !v | f: !(!v | natLt n) -<cloptr,f> a, n: int n):<f> list_vt (a, n)
// end of [list_vt_tabulate_vcloptr]

(* ****** ****** *)

fun{a:vt0p}
list_vt_foreach_funenv
  {v:view} {vt:viewtype} {n:int} {f:eff}
  (pf: !v | xs: !list_vt (a, n), f: !(!v | &a, !vt) -<f> void, env: !vt)
  :<f> void
// end of [list_vt_foreach_funenv]

fun{a:vt0p}
list_vt_foreach_fun {n:int} {f:eff}
  (xs: !list_vt (a, n), f: (&a) -<fun,f> void):<f> void
// end of [list_vt_foreach_fun]

fun{a:vt0p}
list_vt_foreach_vclo {v:view} {n:int} {f:eff}
  (pf: !v | xs: !list_vt (a, n), f: &(!v | &a) -<clo,f> void):<f> void
// end of [list_vt_foreach_vclo]

fun{a:t0p}
list_vt_foreach_cloptr {n:int} {f:eff}
  (xs: !list_vt (a, n), f: !(&a) -<cloptr,f> void):<f> void
// end of [list_vt_foreach_cloptr]
fun{a:t0p}
list_vt_foreach_vcloptr {v:view} {n:int} {f:eff}
  (pf: !v | xs: !list_vt (a, n), f: !(!v | &a) -<cloptr,f> void):<f> void
// end of [list_vt_foreach_vcloptr]

(* ****** ****** *)

fun{a:vt0p}
list_vt_iforeach_funenv
  {v:view} {vt:viewtype} {n:int} {f:eff} (
  pf: !v
| xs: !list_vt (a, n), f: (!v | natLt n, &a, !vt) -<fun,f> void, env: !vt
) :<f> void // end of [list_vt_iforeach_funenv]

fun{a:vt0p}
list_vt_iforeach_fun {n:int} {f:eff}
  (xs: !list_vt (a, n), f: (natLt n, &a) -<fun,f> void):<f> void
// end of [list_vt_iforeach_fun]

fun{a:vt0p}
list_vt_iforeach_vclo {v:view} {n:int} {f:eff}
  (pf: !v | xs: !list_vt (a, n), f: &(!v | natLt n, &a) -<clo,f> void):<f> void
// end of [list_vt_iforeach_vclo]

fun{a:t0p}
list_vt_iforeach_cloptr {n:int} {f:eff}
  (xs: !list_vt (a, n), f: !(natLt n, &a) -<cloptr,f> void):<f> void
// end of [list_vt_iforeach_cloptr]
fun{a:t0p}
list_vt_iforeach_vcloptr {v:view} {n:int} {f:eff}
  (pf: !v | xs: !list_vt (a, n), f: !(!v | natLt n, &a) -<cloptr,f> void):<f> void
// end of [list_vt_iforeach_vcloptr]

(* ****** ****** *)

fun{a:vt0p}
list_vt_mergesort {n:int}
  (xs: list_vt (a, n), cmp: &(&a, &a) -<clo> int):<> list_vt (a, n)
// end of [list_vt_mergesort]

(*
// HX: if needed, this one is more general:
fun{a:vt0p}
list_vt_mergesort {v:view} {n:int}
  (pf: !v | xs: list_vt (a, n), cmp: &(!v | &a, &a) -<clo> int):<> list_vt (a, n)
// end of [list_vt_mergesort]
*)

(* ****** ****** *)
//
// HX:
//
// This one essentially copies a given list into an array; then it sorts
// the array and copies it back into the list; then it frees up the array.
//
// Note that [libc/CATS/stdlib.cats] is needed. It is required that [cmp] be a
// function here as the qsort in stdlib is the underlying implementation.
//
fun{a:vt0p}
list_vt_quicksort {n:int} (xs: !list_vt (a, n), cmp: (&a, &a) -<fun> int):<> void
// end of [list_vt_quicksort]

(* ****** ****** *)

#if VERBOSE_PRELUDE #then
#print "Loading [list_vt.sats] finishes!\n"
#endif // end of [VERBOSE_PRELUDE]

(* end of [list_vt.sats] *)
