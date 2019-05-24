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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February 2008
//
(* ****** ****** *)

// 
// ats_solver_fm:  solving linear constraints with the Fourier-Motzkin
// variable elimination method. This implementation is largely adopted
// from an earlier implementation for DML (done in 1998)
//

(* ****** ****** *)

staload IntInf = "ats_intinf.sats"

(* ****** ****** *)

abst@ype i0nt = int

val i0nt_0 : i0nt
val i0nt_1 : i0nt
val i0nt_neg_1 : i0nt

fun i0nt_of_int
  (_: int): i0nt = "atsopt_solver_fm_i0nt_of_int"
fun i0nt_of_intinf
  (_: $IntInf.intinf_t): i0nt = "atsopt_solver_fm_i0nt_of_intinf"

(* ****** ****** *)

fun gt_i0nt_int (_: i0nt, _: int):<> bool = "atsopt_solver_fm_gt_i0nt_int"
overload > with gt_i0nt_int

fun gte_i0nt_int (_: i0nt, _: int):<> bool = "atsopt_solver_fm_gte_i0nt_int"
overload >= with gte_i0nt_int

fun lt_i0nt_int (_: i0nt, _: int):<> bool = "atsopt_solver_fm_lt_i0nt_int"
overload < with lt_i0nt_int

fun lte_i0nt_int (_: i0nt, _: int):<> bool = "atsopt_solver_fm_lte_i0nt_int"
overload <= with lt_i0nt_int

fun eq_i0nt_int (_: i0nt, _: int):<> bool = "atsopt_solver_fm_eq_i0nt_int"
overload = with eq_i0nt_int

fun neq_i0nt_int (_: i0nt, _: int):<> bool = "atsopt_solver_fm_neq_i0nt_int"
overload <> with neq_i0nt_int

//

fun gt_i0nt_i0nt (_: i0nt, _: i0nt):<> bool = "atsopt_solver_fm_gt_i0nt_i0nt"
overload > with gt_i0nt_i0nt

fun lt_i0nt_i0nt (_: i0nt, _: i0nt):<> bool = "atsopt_solver_fm_lt_i0nt_i0nt"
overload < with lt_i0nt_i0nt

//

fun neg_i0nt (_: i0nt):<> i0nt = "atsopt_solver_fm_neg_i0nt"
overload ~ with neg_i0nt

fun add_i0nt_i0nt (_: i0nt, _: i0nt):<> i0nt = "atsopt_solver_fm_add_i0nt_i0nt"
overload + with add_i0nt_i0nt

fun sub_i0nt_i0nt (_: i0nt, _: i0nt):<> i0nt = "atsopt_solver_fm_sub_i0nt_i0nt"
overload - with sub_i0nt_i0nt

fun mul_i0nt_i0nt (_: i0nt, _: i0nt):<> i0nt = "atsopt_solver_fm_mul_i0nt_i0nt"
overload * with mul_i0nt_i0nt

fun div_i0nt_i0nt (_: i0nt, _: i0nt):<> i0nt = "atsopt_solver_fm_div_i0nt_i0nt"
overload / with div_i0nt_i0nt

//

fun succ_i0nt (_: i0nt):<> i0nt = "atsopt_solver_fm_succ_i0nt"
overload succ with succ_i0nt

fun pred_i0nt (_: i0nt):<> i0nt = "atsopt_solver_fm_pred_i0nt"
overload pred with pred_i0nt

//

fun mod_i0nt_i0nt
  (_: i0nt, _: i0nt):<> i0nt = "atsopt_solver_fm_mod_i0nt_i0nt"
fun gcd_i0nt_i0nt
  (_: i0nt, _: i0nt):<> i0nt = "atsopt_solver_fm_gcd_i0nt_i0nt"

//

fun fprint_i0nt {m:file_mode}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, x: i0nt): void
  = "atsopt_solver_fm_fprint_i0nt"

fun print_i0nt (x: i0nt): void

(* ****** ****** *)

typedef intvec (n:int) = @[i0nt][n]

// initialized with zeros
fun intvec_ptr_make {n: nat}
  (n: int n):<> [l:addr] @(free_gc_v (i0nt?, n, l), intvec n @ l | ptr l)
  = "atsopt_solver_fm_intvec_ptr_make"

fun fprint_intvec
  {m:file_mode} {n:nat} (
  pf_mod: file_mode_lte (m, w) | out: &FILE m, vec: &intvec n, n: int n
) : void // end of [fprint_intvec]

fun print_intvec {n:nat} (vec: &intvec n, n: int n): void
fun prerr_intvec {n:nat} (vec: &intvec n, n: int n): void

overload print with print_intvec
overload prerr with prerr_intvec

(* ****** ****** *)

absviewtype intvecptr_t (n:int) // a (read-only) pointer type

fun intvecptr_make_view_ptr {n:pos} {l:addr}
  (_: free_gc_v (i0nt?, n, l), _: intvec n @ l | _: ptr l)
  :<> intvecptr_t n = "atsopt_solver_fm_intvecptr_make_view_ptr"
// end of [intvecptr_make_view_ptr]

fun intvecptr_free {n:int} (ivp: intvecptr_t n): void
  = "atsopt_solver_fm_intvecptr_free"

fun intvecptr_get {n:pos} (vec: !intvecptr_t n, ind: natLt n):<> i0nt
overload [] with intvecptr_get

fun fprint_intvecptr {m:file_mode} {n:nat} (
    pf_mod: file_mode_lte (m, w)
  | out: &FILE m
  , ivp: !intvecptr_t n
  , n: int n
  ) : void

(* ****** ****** *)
(*
** knd: eq/neq: 1/~1; gte/lt: 2/~2
*)
dataviewtype icstr (int) =
  | {n:pos} {l:addr}
    ICvec (n) of (int(*knd*), intvecptr_t n)
  | {n:pos} {s:nat} (* knd: conj/disj: 0/1 *)
    ICveclst (n) of (int(*knd*), icstrlst (n, s))
// end of [icstr]

where icstrlst (n:int, s: int) = list_vt (icstr n, s)

viewtypedef icstrlst (n:int) = [s:nat] icstrlst (n, s)

fun icstrlst_free {n:pos} (ics: icstrlst n): void

(* ****** ****** *)

fun fprint_icstr {m:file_mode} {n:pos}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, ic: !icstr n, n: int n): void

fun fprint_icstrlst {m:file_mode} {n:pos} {s:nat}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, ics: !icstrlst (n, s), n: int n): void

fun print_icstr {n:pos} (ic: !icstr n, n: int n): void
overload print with print_icstr

fun print_icstrlst {n:pos} (ics: !icstrlst n, n: int n): void
overload print with print_icstrlst

(* ****** ****** *)

fun icstr_negate {n:pos} (ic: icstr n): icstr n
fun icstrlst_negate {n:pos} {s:nat} (ics: icstrlst (n, s)): icstrlst (n, s)

(* ****** ****** *)

// [~1]: a contradiction is reached; [0]: unsolved constraints
fun icstrlst_solve {n:pos} (ics: &icstrlst n, n: int n): intBtw (~1, 1)

(* ****** ****** *)

(* end of [ats_solver_fm.sats] *)
