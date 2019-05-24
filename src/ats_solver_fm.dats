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

%{^
#include "ats_solver_fm.cats"
%}

(* ****** ****** *)

staload Err = "ats_error.sats"
fn prerr_interror () = prerr "INTERNAL ERROR (ats_solver_fm)"

(* ****** ****** *)

staload Lst = "ats_list.sats"

(* ****** ****** *)

staload "ats_solver_fm.sats"

(* ****** ****** *)

implement i0nt_0 = i0nt_of_int 0
implement i0nt_1 = i0nt_of_int 1
implement i0nt_neg_1 = i0nt_of_int (~1)

implement print_i0nt (x) = print_mac (fprint_i0nt, x)

(* ****** ****** *)

implement
fprint_intvec {m} {n} (pf_mod | out, vec, n) = let
  fun aux {i:nat | i <= n} .<n-i>.
    (out: &FILE m, vec: &intvec n, n: int n, i: int i): void = begin
    if (i < n) then begin
      if i > 0 then fprint1_string (pf_mod | out, ", ");
      fprint_i0nt (pf_mod | out, vec.[i]); aux (out, vec, n, i+1)
    end
  end // end of [aux]
in
  aux (out, vec, n, 0)
end // end of [fprint_intvec]

(* ****** ****** *)

implement
print_intvec (vec, n) = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
in
  fprint_intvec (file_mode_lte_w_w | !ptr_stdout, vec, n);
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_intvec]

implement
prerr_intvec (vec, n) = let
  val (pf_stderr | ptr_stderr) = stderr_get ()
in
  fprint_intvec (file_mode_lte_w_w | !ptr_stderr, vec, n);
  stderr_view_set (pf_stderr | (*none*))
end // end of [prerr_intvec]

(* ****** ****** *)

fn intvec_ptr_alloc
  {n:nat} (n: int n)
  :<> [l:addr] (
  free_gc_v (i0nt?, n, l), (intvec n)? @ l | ptr l
) =
  array_ptr_alloc_tsz {i0nt} (size1_of_int1 n, sizeof<i0nt>)
// end of [intvec_ptr_alloc]

fn intvec_ptr_free
  {n:int} {l:addr} (
  pf_gc: free_gc_v (i0nt?, n, l), pf_arr: (intvec n)? @ l | p: ptr l
) :<> void =
  array_ptr_free {i0nt?} (pf_gc, pf_arr | p)
// end of [intvec_ptr_free]

(* ****** ****** *)

local

assume intvecptr_t (n:int) =
  [l:addr] @(free_gc_v (i0nt?, n, l), intvec n @ l | ptr l)
// end of [intvecptr_t]

in

implement
fprint_intvecptr (pf_mod | out, ivp, n) = let
  prval pf_arr = ivp.1
  val () = fprint_intvec (pf_mod | out, !(ivp.2), n)
  prval () = ivp.1 := pf_arr
in
  // empty
end // end of [fprint_intvecptr]

end // end of [local]

(* ****** ****** *)

fun icstr_free {n:pos} (ic: icstr n): void = begin
  case+ ic of
  | ~ICvec (_, ivp) => intvecptr_free (ivp)
  | ~ICveclst (_, ics) => icstrlst_free ics
end // end of [icstr_free]

implement
icstrlst_free (ics) = begin case+ ics of
  | ~list_vt_cons (ic, ics) => (icstr_free ic; icstrlst_free ics)
  | ~list_vt_nil () => ()
end // end of [icstrlst_free]

(* ****** ****** *)

implement
fprint_icstr {m} {n}
  (pf_mod | out, ic, n) = let
  macdef prstr (s) = fprint1_string (pf_mod | out, ,(s))
in
  case+ ic of
  | ICvec (knd, !ivp) => begin
      prstr "ICvec("; prstr "knd=";
      fprint1_int (pf_mod | out, knd);
      prstr "; ";
      fprint_intvecptr (pf_mod | out, !ivp, n);
      prstr ")";
      fprint_newline (pf_mod | out);
      fold@ ic
    end // end of [ICvec]
  | ICveclst (knd, !ics) => begin
      prstr "ICveclst("; prstr "knd=";
      fprint1_int (pf_mod | out, knd);
      prstr "; ";
      fprint_icstrlst (pf_mod | out, !ics, n);
      prstr ")";
      fprint_newline (pf_mod | out);
      fold@ ic
    end // end of [ICveclst]
end // end of [fprint_icstr]

implement
fprint_icstrlst {m} {n}
  (pf_mod | out, ics, n) = begin case+ ics of
  | list_vt_cons (!ic, !ics_nxt) => begin
      fprint_icstr (pf_mod | out, !ic, n);
      fprint_icstrlst (pf_mod | out, !ics_nxt, n);
      fold@ ics
    end // end of [list_vt_cons]
  | list_vt_nil () => fold@ ics
end // end of [fprint_icstrlst]

(* ****** ****** *)

implement
print_icstr (ic, n) = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
in
  fprint_icstr (file_mode_lte_w_w | !ptr_stdout, ic, n);
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_icstr]

implement
print_icstrlst (ics, n) = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
in
  fprint_icstrlst (file_mode_lte_w_w | !ptr_stdout, ics, n);
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_icstrlst]

(* ****** ****** *)

local

fun aux {n:pos}
  (ic: !icstr n): void = begin
  case+ ic of
  | ICvec (!knd, _(*ivp*)) => (!knd := 0 - (!knd); fold@ ic)
  | ICveclst (!knd, !ics) => (!knd := 1 - !knd; auxlst (!ics); fold@ ic)
end // end of [aux]

and auxlst {n:pos} {s:nat}
  (ics: !icstrlst (n, s)): void = begin
  case+ ics of
  | list_vt_cons (!ic, !ics_nxt) => (aux (!ic); auxlst (!ics_nxt); fold@ ics)
  | list_vt_nil () => fold@ ics
end // end of [auxlst]

in // in of [local]

implement icstr_negate (ic) = (aux ic; ic)
implement icstrlst_negate (ics) = (auxlst ics; ics)

end // end of [local]

(* ****** ****** *)

dataviewtype intveclst (int) =
  | {n:pos} {l:addr}
    INTVECLSTcons (n) of (
      free_gc_v (i0nt?, n, l), intvec n @ l | ptr l, intveclst n
    ) // end of [INTVECLSTcons]
  | {n:pos} INTVECLSTnil (n)
// end of [intveclst]

fun intveclst_free {n:int}
  (vecs: intveclst n): void = begin
  case+ vecs of
  | ~INTVECLSTcons (pf_gc, pf_arr | p, vecs_nxt) => begin
      intvec_ptr_free (pf_gc, pf_arr | p); intveclst_free (vecs_nxt)
    end // end of [INTVECLSTcons]
  | ~INTVECLSTnil () => ()
end // end of [intveclst_free]

fun fprint_intveclst {m:file_mode} {n:pos}
  (pf_mod: file_mode_lte (m, w) | out: &FILE m, vecs: !intveclst n, n: int n)
  : void = begin case+ vecs of
  | INTVECLSTcons (_, !pf_arr  | p, !vecs_nxt) => let
      prval pf = !pf_arr
      val () = fprint_intvec (pf_mod | out, !p, n)
      prval () = (!pf_arr := pf)
      val () = fprint_newline (pf_mod | out)
      val () = fprint_intveclst (pf_mod | out, !vecs_nxt, n)
    in
      fold@ (vecs)
    end // end of [INTVECLSTcons]
  | INTVECLSTnil () => (fold@ vecs)
end // end of [fprint_intveclst]

fun print_intveclst {n:pos}
  (vecs: !intveclst n, n: int n): void = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
  val () = fprint_intveclst (file_mode_lte_w_w | !ptr_stdout, vecs, n)
  val () = stdout_view_set (pf_stdout | (*none*))
in
  // nothing
end // end of [print_intveclst]

(* ****** ****** *)

#define UNKNOWN (0)
#define TAUTOLOGY (1)
#define CONTRADICTION (~1)

(* ****** ****** *)

fun intvec_coeff_gcd {n:pos}
  (vec: &intvec n, n: int n): i0nt = let
  fun aux {i:nat | i < n} .<i>.
    (vec: &intvec n, i: int i, gcd: &i0nt): void = begin
    if i > 0 then let
      val vi = vec.[i]
    in
      if vi <> 0 then
        if vi <> 1 then let
          val () = (gcd := gcd_i0nt_i0nt (vi, gcd))
        in
          if gcd <> 1 then aux (vec, i-1, gcd) else ()
        end else begin
          gcd := vi // return now!
        end // end of [if]
      else begin
        aux (vec, i-1, gcd)
      end
    end
  end // end of [aux]
  var gcd: i0nt = i0nt_of_int 0  
in
  aux (vec, n-1, gcd); gcd
end // end of [intvec_coeff_gcd]

(* ****** ****** *)

extern
fun intvec_normalize_gte {n:pos} (vec: &intvec n, n: int n): void

implement
intvec_normalize_gte {n} (vec, n) = let
  fun aux {i:int | i < n} .<max(i+1,0)>.
    (vec: &intvec n, i: int i, gcd: i0nt): void = begin
    if i >= 0 then let
      val vi = vec.[i]
      val () = if vi <> 0 then vec.[i] := (vi / gcd) else ()
    in
      aux (vec, i-1, gcd)
    end
  end // end of [aux]
  val gcd = intvec_coeff_gcd (vec, n)
in
  if gcd > 1 then let
    val v0 = vec.[0]
(*
    val () = begin
      print "intvec_normalize_gte: gcd = "; print_i0nt gcd; print_newline ();
      print "intvec_normalize_gte: v0_old = "; print_i0nt v0; print_newline ();
    end
*)
    val () = aux (vec, n-1, gcd)
    val () = begin case+ 0 of
      | _ when v0 >= 0 => vec.[0] := v0 / gcd
      | _ => vec.[0] := succ (v0 - gcd) / gcd
    end // end of [val]
(*
    val v0 = vec.[0]
    val () = begin
      print "intvec_normalize_gte: v0_new = "; print_i0nt v0; print_newline ()
    end
*)
  in
    // empty    
  end
end // end of [intvec_normalize_gte]

(* ****** ****** *)

extern
fun intvec_normalize_eq
  {n:pos} (vec: &intvec n, n: int n): intBtw (~1, 1)
// end of [intvec_normalize_eq]

implement
intvec_normalize_eq {n} (vec, n) = let
  fun aux {i:int | i < n} .<max(i+1,0)>.
    (vec: &intvec n, i: int i, gcd: i0nt): void = begin
    if i >= 0 then let
      val vi = vec.[i]
      val () = if vi <> 0 then vec.[i] := (vi / gcd) else ()
    in
      aux (vec, i-1, gcd)
    end
  end // end of [aux]
  val gcd = intvec_coeff_gcd (vec, n)
in
  if gcd > 1 then let
    val v0 = vec.[0]
  in
    if mod_i0nt_i0nt (v0, gcd) = 0 then (aux (vec, n-1, gcd); 0)
    else ~1 // a contradiction
  end else begin
    0 // there is nothing to be done
  end
end // end of [intvec_normalize_eq]

(* ****** ****** *)

extern
fun intvec_inspect_gte {n:pos} (vec: &intvec n, n: int n): Sgn
// end of [intvec_inspect_gte]

implement
intvec_inspect_gte {n} (vec, n) = let
  fun aux {i:nat | i < n} (vec: &intvec n, i: int i): Sgn =
    if i > 0 then begin
      if vec.[i] <> 0 then UNKNOWN else aux (vec, i-1)
    end else begin
      if vec.[0] >= 0 then TAUTOLOGY else CONTRADICTION
    end
  val sgn = aux (vec, n - 1)
  val () = if sgn = 0 then intvec_normalize_gte (vec, n)
in
  sgn
end // end of [intvec_inspect_gte]

(* ****** ****** *)

extern
fun intveclst_inspect_gte
  {n:pos} (vecs: &intveclst n, n: int n): intBtw (~1, 1)
// end of [intveclst_inspect_gte]

implement
intveclst_inspect_gte (vecs, n) = begin
  case+ vecs of
  | INTVECLSTcons {n} (!pf_gc, !pf_arr | p, !vecs_nxt) => let
      prval pf = !pf_arr
      val sgn = intvec_inspect_gte (!p, n)
      prval () = !pf_arr := pf
    in
      if sgn <> 0 then begin // tautology/contradiction
        intvec_ptr_free (!pf_gc, !pf_arr | p); 
        let val tmp = !vecs_nxt in free@ {n} (vecs); vecs := tmp end;
        if sgn > 0 then intveclst_inspect_gte (vecs, n) else ~1
      end else let
        val ans = intveclst_inspect_gte (!vecs_nxt, n)
      in
        fold@ vecs; ans
      end // end of [if]
    end
  | INTVECLSTnil () => (fold@ vecs; 0)
end // end of [intveclst_inspect_gte]

(* ****** ****** *)

extern
fun intvec_inspect_eq {n:pos} (vec: &intvec n, n: int n): Sgn
// end of [intvec_inspect_eq]

implement
intvec_inspect_eq {n} (vec, n) = let
  fun aux {i:nat | i < n} .<i>. (vec: &intvec n, i: int i): Sgn =
    if i > 0 then begin
      if vec.[i] <> 0 then UNKNOWN else aux (vec, i-1)
    end else begin
      if vec.[0] = 0 then TAUTOLOGY else CONTRADICTION
    end
in
  aux (vec, n - 1)
end // end of [intvec_inspect_eq]

(* ****** ****** *)

(* 
** HX:
** the function returns the index of the coefficient with minimum
** non-zero absolute value
*)

extern
fun intvec_absmin_coeff_index_get
  {n:pos} (vec: &intvec n, n: int n): intBtw (1, n)
// end of [intvec_absmin_coeff_index_get]

implement
intvec_absmin_coeff_index_get {n} (vec, n) = let
  fun aux1 {i,i0: nat | 1 <= i0; i <= i0; i0 < n} .<i>.
    (vec: &intvec n, i: int i, i0: int i0, c0: &i0nt): intBtw (1, n) =
    if c0 = 1 then i0
    else if i > 0 then let
      val vi = vec.[i]
      val vi = (if vi >= 0 then vi else ~vi): i0nt
      var flag: int = 0
(*
      val () = begin
        print "aux1: i = "; print i; print_newline ();
        print "aux1: vi = "; print_i0nt vi; print_newline ();
        print "aux1: i0 = "; print i0; print_newline ();
        print "aux1: c0 = "; print_i0nt c0; print_newline ();
      end
*)
      val () = begin
        if vi > 0 then (if c0 > vi then (c0 := vi; flag := 1))
      end
    in
      if flag > 0 then begin
        aux1 (vec, i-1,  i, c0)
      end else begin
        aux1 (vec, i-1, i0, c0)
      end
    end else begin
      i0 // the vec.[i0] should not be zero!
    end
  fun aux2 {i: nat | i < n} .<i>. 
    (vec: &intvec n, n: int n, i: int i): intBtw (1, n) =
    if i > 0 then let
      val vi = vec.[i]
    in
      if vi > 0 then
        let var c0: i0nt =  vi in aux1 (vec, i-1, i, c0) end
      else if vi < 0 then
        let var c0: i0nt = ~vi in aux1 (vec, i-1, i, c0) end
      else aux2 (vec, n, i-1)
    end else begin
      prerr_interror ();
      prerr ": intvec_absmin_coeff_index_get: all coefficients are zero: ";
      prerr_newline ();
      prerr "vec = "; prerr (vec, n); prerr_newline ();
      $Err.abort ()
    end // end of [if]
  val ind = aux2 (vec, n, n - 1)
(*
  val () = let
    val vind = vec.[ind] in
    if vind < ~1 orelse vind > 1 then begin
      print "intvec_absmin_coeff_index_get: vec = ";
      print (vec, n); print_newline ();
      print "intvec_absmin_coeff_index_get: ind = ";
      print ind; print_newline ();
      print "intvec_absmin_coeff_index_get: vind = ";
      print_i0nt vind; print_newline ();
    end // end of [if]
  end // end of [val]
*)
in
  ind
end // end of [intvec_absmin_coeff_index_get]

(* ****** ****** *)

extern
fun intvec_copy
  {n:nat} (
  vec: &intvec n, n: int n
) :<> [l:addr] (
  free_gc_v (i0nt?, n, l), intvec n @ l | ptr l
) = "ats_solver_fm_intvec_copy"

implement
intvec_copy (vec, n) = let
  val (pfgc, pfarr | p) = intvec_ptr_alloc (n)
  val () = array_ptr_copy_tsz {i0nt} (vec, !p, size1_of_int1 n, sizeof<i0nt>)
in
  @(pfgc, pfarr | p)
end // end of [intvec_copy]

(* ****** ****** *)

extern
fun intvecptr_copy
  {n:nat} (
  vec: !intvecptr_t n, n: int n
) :<> [l:addr] (
  free_gc_v (i0nt?, n, l), intvec n @ l | ptr l
) = "ats_solver_fm_intvec_copy"

(* ****** ****** *)

extern
fun intvec_negate {n:nat} (vec: &intvec n, n: int n): void

implement
intvec_negate {n}
  (vec, n) = let
  var i = n - 1 in
  while* // going downward
    {i:int | ~1 <= i; i < n} .<i+1>. (i: int i) => (i >= 0) begin
      vec.[i] := ~(vec.[i]) ; i := i - 1 ;
    end // end of [while]
end // end of [intvec_negate]

(* ****** ****** *)

extern
fun intvec_scale {n:nat} (vec: &intvec n, n: int n, c: i0nt):<> void

implement
intvec_scale {n} (vec, n, c) = begin
//
if (c <> 1) then let
  var i = n - 1
in
  while* // going downward
    {i:int | ~1 <= i; i < n} .<i+1>. (i: int i) => (i >= 0) begin
      vec.[i] := c * vec.[i] ; i := i - 1 ;
    end // end of [while]
end // end if [if]
//
end // end of [intvec_scale]

(* ****** ****** *)

extern
fun intvec_copy_and_scale
  {n:nat} (
  vec: &intvec n, n: int n, c: i0nt
) :<> [l:addr] (
  free_gc_v (i0nt?, n, l), intvec n @ l | ptr l
) // end of [intvec_copy_and_scale]

implement
intvec_copy_and_scale
  (vec, n, c) = begin
  if c <> 1 then let
    // this could be done in one-loop, but ...
    val (pf_gc, pf_arr | p) = intvec_copy (vec, n)
    val () = intvec_scale (!p, n, c)
  in
    @(pf_gc, pf_arr | p)
  end else begin
    intvec_copy (vec, n)
  end
end // end of [intvec_copy_and_scale]

(* ****** ****** *)
//
// HX: [vec1 := vec1 + vec2]
//
extern
fun intvec_add_by {n:nat}
  (vec1: &intvec n, vec2: &intvec n, n: int n):<> void
// end of [intvec_add_by]

implement
intvec_add_by {n} (vec1, vec2, n) = let
  var i = n - 1
in
  while* // going downward
    {i:int | ~1 <= i; i < n} .<i+1>. (i: int i) => (i >= 0) begin
      vec1.[i] := vec1.[i] + vec2.[i] ; i := i - 1 ;
    end // end of [while]
end // end of [intvec_add_by]

(* ****** ****** *)

//
// HX: [vec1 := vec1 - vec2]
//
extern
fun intvec_sub_by {n:nat}
  (vec1: &intvec n, vec2: &intvec n, n: int n):<> void
// end of [intvec_sub_by]

implement
intvec_sub_by {n} (vec1, vec2, n): void = let
  var i = n - 1
in
  while* // going downward
    {i:int | ~1 <= i; i < n} .<i+1>. (i: int i) => (i >= 0) begin
      vec1.[i] := vec1.[i] - vec2.[i] ; i := i - 1 ;
    end // end of [while]
end // end of [intvec_sub_by]

(* ****** ****** *)

//
// HX: [vec1 := vec1 + c * vec2]
//
extern
fun intvec_add_by_scale {n:nat}
  (vec1: &intvec n, vec2: &intvec n, n: int n, c: i0nt):<> void
// end of [intvec_add_by_scale]

implement intvec_add_by_scale {n} (vec1, vec2, n, c) = begin
  if c = 0 then () // do nothing
  else if c = 1 then begin
    intvec_add_by (vec1, vec2, n)
  end else let
    var i = n - 1; val () = while* // going downward
      {i:int | ~1 <= i; i < n} .<i+1>. (i: int i) => (i >= 0) begin
        vec1.[i] := vec1.[i] + c * vec2.[i] ; i := i - 1 ;
      end // end of [while]
  in
    // empty
  end // end of [if]
end // end of [intvec_add_by_scale]
  
(* ****** ****** *)

extern
fun intvec_combine_at
  {n,i:int | 0 < i; i < n} (
  _pos: &intvec n
, _neg: &intvec n
, n: int n, i: int i
) :<> [l:addr] (
  free_gc_v (i0nt?, n, l), intvec n @ l | ptr l
) // end of [intvec_combine_at]

implement
intvec_combine_at (
  vec_pos, vec_neg, n, i
) = let
  val c_pos = vec_pos.[i] and c_neg = ~(vec_neg.[i])
  val (pf_gc, pf_arr | p) = intvec_copy_and_scale (vec_neg, n, c_pos)
  val () = intvec_add_by_scale (!p, vec_pos, n, c_neg)
in
  @(pf_gc, pf_arr | p)
end // end of [intvec_combine_at]

(* ****** ****** *)
//
// HX: [~1] is returned if contradiction is reached; otherwise, [0] is returned
//
extern
fun intveclst_split_at
  {n,i:int | 0 < i; i < n}
  (vecs: &intveclst n, n: int n, i: int i): intBtw (~1, 1)
// end of [intveclst_split_at]

implement
intveclst_split_at
  {n,i} (vecs, n, i) = let
//
stadef ivs = intveclst
//
fun auxbeg ( // split [vecs] into three groups
  poss: &ivs n, neus: &ivs n, negs: &ivs n, vecs: ivs n
) :<cloptr1> void = let
  val fst = vecs
in
//
case+ fst of
| INTVECLSTcons
    (!pf_gc, !pf_arr | p, !nxt) => let
    prval pf = !pf_arr; val vi = p->[i]; prval () = !pf_arr := pf
    val vecs = !nxt
    val () = (
      if vi > 0 then begin
        !nxt := poss; poss := fst; fold@ poss
      end else if vi < 0 then begin
        !nxt := negs; negs := fst; fold@ negs
      end else begin
        !nxt := neus; neus := fst; fold@ neus
      end // end of [if]
    ) : void // end of [val]
  in
    auxbeg (poss, neus, negs, vecs)
  end // end of [INTVECLSTcons]
| ~INTVECLSTnil () => ()
//
end // end of [auxbeg]
//
fun auxcomb (
// return [~1] if contradiction is reached
  neus: &ivs n, neg: &intvec n, poss: &ivs n
) :<cloptr1> intBtw (~1, 1) = begin
  case+ poss of
  | INTVECLSTcons
      (_, !pf_arr | p, !poss_nxt) => let
      prval pf = !pf_arr
      val @(pf_new_gc, pf_new_arr | p_new) = intvec_combine_at (!p, neg, n, i)
      val sgn = intvec_inspect_gte (!p_new, n)
      prval () = !pf_arr := pf
      val () = (
        if sgn <> 0 then begin // tautology or contradiction
          intvec_ptr_free (pf_new_gc, pf_new_arr | p_new)
        end else begin
          neus := INTVECLSTcons (pf_new_gc, pf_new_arr | p_new, neus)
        end // end of [if]
      ) : void // end of [val]
    in
      if (sgn >= 0) then begin
        let val ans = auxcomb (neus, neg, !poss_nxt) in fold@ poss; ans end
      end else begin
        fold@ (poss); ~1
      end (* end of [if] *)
    end // end of [INTVECLSTcons]
  | INTVECLSTnil () => (fold@ (poss); 0)
end // end of [auxcomb]
//
// HX: [~1] is returned if contradiction is reached
//
fun auxcomblst (
  neus: &ivs n, poss: &ivs n, negs: ivs n
) :<cloptr1> intBtw (~1, 1) = begin
  case+ negs of
  | ~INTVECLSTcons
      (pf_gc, pf_arr | p, negs_nxt) => let
      val ans = auxcomb (neus, !p, poss)
      val () = intvec_ptr_free (pf_gc, pf_arr | p)
    in
      if ans >= 0 then begin
        auxcomblst (neus, poss, negs_nxt)
      end else let
        val () = intveclst_free (negs_nxt) in ans
      end (* end of [if] *)
    end // end of [INTVECLSTcons]
  | ~INTVECLSTnil () => 0
end // end of [auxcomblst]
//
var poss: ivs n = INTVECLSTnil ()
and neus: ivs n = INTVECLSTnil ()
and negs: ivs n = INTVECLSTnil ()
//
val () =
  auxbeg (poss, neus, negs, vecs)
// end of [val]
val ans = auxcomblst (neus, poss, negs)
val () = intveclst_free poss
//
in
  vecs := neus; ans
end // end of [intveclst_split_at]

(* ****** ****** *)

extern
fun intveclst_solve
  {n:pos} (vecs: intveclst n, n: int n): intBtw (~1, 1)
// end of [intveclst_solve]

implement
intveclst_solve {n} (vecs, n) = let
  fun aux_solve
    (vecs: &intveclst n, n: int n): intBtw (~1, 1) = begin
    case+ vecs of
    | INTVECLSTcons
        (_(*pf_gc*), !pf_arr | p, _(*p_vecs*)) => let
        prval pf = !pf_arr
        val i (* 0 < i < n *) = intvec_absmin_coeff_index_get (!p, n)
        prval () = (!pf_arr := pf; fold@ vecs)
        val ans = intveclst_split_at (vecs, n, i)
      in
        if ans >= 0 then aux_solve (vecs, n) else ~1
      end
    | INTVECLSTnil () => (fold@ vecs; 0)
  end // end of [aux_solve]
(*
  val () = begin
    print "intveclst_solve: vecs =\n"; print_intveclst (vecs, n); print_newline ();
  end // end of [val]
*)
  var vecs: intveclst n = vecs
  val ans = aux_solve (vecs, n)
  val () = intveclst_free vecs
in
  ans
end // end of [intveclst_solve]

(* ****** ****** *)

extern
fun intvec_elim_at {n,i:int | 0 < i; i < n}
  (vec: &intvec n, vec_eq: &intvec n, n: int n, i: int i): void
// end of [intvec_elim_at]

implement
intvec_elim_at (vec, vec_eq, n, i) = let
  val vi = vec.[i] and vi_eq = vec_eq.[i]
in
  if vi = 0 then () else begin
    if vi_eq >= 0 then begin
      intvec_scale (vec, n, vi_eq); intvec_add_by_scale (vec, vec_eq, n, ~vi)
    end else begin
      intvec_scale (vec, n, ~vi_eq); intvec_add_by_scale (vec, vec_eq, n, vi)
    end
  end
end // end of [intvec_elim_at]

extern
fun intveclst_elim_at {n,i:int | 0 < i; i < n}
  (vecs: !intveclst n, vec_eq: &intvec n, n: int n, i: int i): void
// end of [intveclst_elim_at]

implement
intveclst_elim_at (vecs, vec_eq, n, i) = begin
  case+ vecs of
  | INTVECLSTcons (_, !pf_arr | p, !vecs_nxt) => let
      prval pf = !pf_arr
      val () = intvec_elim_at (!p, vec_eq, n, i)
      prval () = !pf_arr := pf
      val () = intveclst_elim_at (!vecs_nxt, vec_eq, n, i)
    in
      fold@ vecs
    end
  | INTVECLSTnil () => fold@ vecs
end // end of [intveclst_elim_at]

(* ****** ****** *)

dataviewtype
intveclst1 (int) =
  | {n:pos} {l:addr}
    INTVECLST1cons (n) of (
      free_gc_v (i0nt?, n, l), intvec n @ l
    | int(*stamp*), ptr l, intBtw (0, n) (*0:gte/1+:eq*), intveclst1 n
    ) // end of [INTVECLST1cons]
  | {n:pos} INTVECLST1mark (n) of intveclst1 n
  | {n:pos} INTVECLST1nil (n)
// end of [intveclst1]

fun intveclst1_free {n:int} (v1ecs: intveclst1 n): void = begin
  case+ v1ecs of
  | ~INTVECLST1cons (pf_gc, pf_arr | _, p, _, v1ecs) => begin
      intvec_ptr_free (pf_gc, pf_arr | p); intveclst1_free (v1ecs)
    end
  | ~INTVECLST1mark (v1ecs) => intveclst1_free v1ecs
  | ~INTVECLST1nil () => ()
end // end of [intveclst_free]

fun intveclst1_backtrack {n:pos}
  (v1ecs: intveclst1 n): intveclst1 n = begin case+ v1ecs of
  | ~INTVECLST1cons (pf_gc, pf_arr | _, p, _, v1ecs) => begin
      intvec_ptr_free (pf_gc, pf_arr | p); intveclst1_backtrack v1ecs
    end // end of [INTVECLST1cons]
  | ~INTVECLST1mark (v1ecs) => v1ecs
  | ~INTVECLST1nil () => INTVECLST1nil ()
end // end of [intveclst1_backtrack]

(* ****** ****** *)

fun fprint_intveclst1
  {m:file_mode} {n:pos} (
  pf_mod: file_mode_lte (m, w)
| out: &FILE m, v1ecs: !intveclst1 n, n: int n
) : void = begin case+ v1ecs of
  | INTVECLST1cons (_, !pf_arr  | stamp, p, i, !v1ecs_nxt) => let
      prval pf = !pf_arr
      val () = fprintf1_exn (pf_mod | out, "(%i;%i): ", @(stamp,i))
      val () = fprint_intvec (pf_mod | out, !p, n)
      prval () = (!pf_arr := pf)
      val () = fprint_newline (pf_mod | out)
      val () = fprint_intveclst1 (pf_mod | out, !v1ecs_nxt, n)
    in
      fold@ (v1ecs)
    end // end of [INTVECLST1cons]
  | INTVECLST1mark (!v1ecs_nxt) => let
      val () = fprint_intveclst1 (pf_mod | out, !v1ecs_nxt, n)
    in
      fold@ (v1ecs)
    end
  | INTVECLST1nil () => (fold@ v1ecs)
end // end of [fprint_intveclst1]

fun print_intveclst1
  {n:pos} (
  v1ecs: !intveclst1 n, n: int n
): void = let
  val (pf_stdout | ptr_stdout) = stdout_get ()
in
  fprint_intveclst1 (file_mode_lte_w_w | !ptr_stdout, v1ecs, n);
  stdout_view_set (pf_stdout | (*none*))
end // end of [print_intveclst1]

(* ****** ****** *)

extern
fun intvec_elimlst {n:pos} (
  stamp: int, vec: &intvec n, v1ecs_eq: !intveclst1 n, n: int n
) : void // end of [intvec_elimlst]

implement
intvec_elimlst (
  stamp0, vec, v1ecs_eq, n
) = begin
  case+ v1ecs_eq of
  | INTVECLST1cons (
      _, !pf_arr | stamp, p, i, !v1ecs_eq_nxt
    ) => begin
      if stamp0 <= stamp then let
        // Note: elimination must be done in the reverse order!
        // It was done incorrectly and a bug occurred.
        val () = intvec_elimlst (stamp0, vec, !v1ecs_eq_nxt, n)
        prval pf = !pf_arr
        val () = assert (i > 0)
        val () = intvec_elim_at (vec, !p, n, i)
        prval () = !pf_arr := pf
      in
        fold@ v1ecs_eq
      end else let
        val () = intvec_elimlst (stamp0, vec, !v1ecs_eq_nxt, n)
      in
        fold@ v1ecs_eq
      end (* end of [if] *)
    end // end of [INTVECLST1cons]
  | INTVECLST1mark (!v1ecs_eq_nxt) => let
      val () = intvec_elimlst (stamp0, vec, !v1ecs_eq_nxt, n)
    in
      fold@ v1ecs_eq
    end // end of [INTVECLST1mark]
  | INTVECLST1nil () => (fold@ v1ecs_eq)
end // end of [intvec_elimlst]

(* ****** ****** *)

extern
fun intveclst_make {n:nat} (
  v1ecs: !intveclst1 n, v1ecs_eq: !intveclst1 n, n: int n
) : intveclst n // end of [intveclst_make]

implement
intveclst_make {n}
  (v1ecs, v1ecs_eq, n) = let
//
  fun loop (
      v1ecs: !intveclst1 n
    , v1ecs_eq: !intveclst1 n
    , n: int n
    , res: &(intveclst n?) >> intveclst n
    ) : void = begin case+ v1ecs of
    | INTVECLST1cons (_, !pf_arr | stamp, p, _, !v1ecs_nxt) => let
        prval pf = !pf_arr
        val (pf_new_gc, pf_new_arr | p_new) = intvec_copy (!p, n)
        prval () = !pf_arr := pf
        val () = intvec_elimlst (stamp, !p_new, v1ecs_eq, n)
        val () = res := INTVECLSTcons (pf_new_gc, pf_new_arr | p_new, ?)
        val+ INTVECLSTcons (_, _ | _, !res_nxt) = res
      in
        loop (!v1ecs_nxt, v1ecs_eq, n, !res_nxt); fold@ v1ecs; fold@ res
      end // end of [INTVECLST1cons]
    | INTVECLST1mark (!v1ecs_nxt) => begin
        loop (!v1ecs_nxt, v1ecs_eq, n, res); fold@ v1ecs
      end // end of [INTVECLST1mark]
    | INTVECLST1nil () => begin
        res := INTVECLSTnil (); fold@ v1ecs
      end // end of [INTVECLST1nil]
  end // end of [loop]
//
  var vecs: intveclst n // uninitialized
  val () = loop (v1ecs, v1ecs_eq, n, vecs)
//
in
  vecs
end // end of [intveclst_make]

(* ****** ****** *)

implement
icstrlst_solve {n} (ics, n) = let
//
fun aux_main {s:nat} (
    stamp: int
  , v1ecs: &intveclst1 n
  , v1ecs_eq: &intveclst1 n
  , n: int n
  , ics: &icstrlst (n, s)
  ) : intBtw (~1, 1) = begin case+ ics of
  | list_vt_cons (!ic, !ics_nxt) => begin case+ !ic of
    | ICvec (knd, !ivp) => begin case+ knd of
      | _ when knd = 2(*gte*) orelse knd(*lt*) = ~2 => let
          val @(pf_gc, pf_arr | p) = intvecptr_copy (!ivp, n)
          val () =
            if knd < 0 then begin // knd = ~2(*lt*)
              intvec_negate (!p, n); p->[0] := pred (p->[0])
            end
          val () = intvec_elimlst (0(*stamp*), !p, v1ecs_eq, n)
          val sgn = intvec_inspect_gte (!p, n)
        in
          if sgn > 0 then let // tautology
            val () = intvec_ptr_free (pf_gc, pf_arr | p)
            val ans = aux_main (stamp, v1ecs, v1ecs_eq, n, !ics_nxt)
          in
            fold@ (!ic); fold@ (ics); ans
          end else if sgn < 0 then let // contradiction
            val () = intvec_ptr_free (pf_gc, pf_arr | p)
          in
            fold@ (!ic); fold@ (ics); ~1(*solved*)
          end else let
            val () = v1ecs :=
              INTVECLST1cons (pf_gc, pf_arr | stamp, p, 0(*dummy*), v1ecs)
            var vecs = intveclst_make (v1ecs, v1ecs_eq, n)
            val ans1 = intveclst_inspect_gte (vecs, n)
            val ans: intBtw (~1, 1) =
              if ans1 >= 0 then let
                val ans2 = intveclst_solve (vecs, n)
              in
                if ans2 >= 0 then
                  aux_main (stamp+1, v1ecs, v1ecs_eq, n, !ics_nxt)
                else ~1
              end else let
                val () = intveclst_free (vecs)
              in
                ~1 // a contradiction is reached!
              end (* end of [if] *)
          in
            fold@ (!ic); fold@ (ics); ans
          end (* end of [if] *)
        end // end of [2(*gte*) and ~2(*lt*)]
      | _ when knd = 1(*eq*) => let
          val (pf_gc, pf_arr | p) = intvecptr_copy (!ivp, n)
          val () = intvec_elimlst (0(*stamp*), !p, v1ecs_eq, n)
          val sgn = intvec_inspect_eq (!p, n)
        in
          if sgn > 0 then let // tautology
            val () = intvec_ptr_free (pf_gc, pf_arr | p)
            val ans = aux_main (stamp, v1ecs, v1ecs_eq, n, !ics_nxt)
          in
            fold@ (!ic); fold@ (ics); ans           
          end else if sgn < 0 then let // contradiction
            val () = intvec_ptr_free (pf_gc, pf_arr | p)
          in
            fold@ (!ic); fold@ (ics); ~1(*solved*)
          end else let
            val i = intvec_absmin_coeff_index_get (!p, n)
            var vi: i0nt = p->[i]; val () = if vi < 0 then vi := ~vi
            var ans: intBtw (~1, 1) = 0
            val () = if vi > 1 then ans := intvec_normalize_eq (!p, n)
            var vecs: (intveclst n)?
            val () =
              if :(vecs: intveclst n) => ans >= 0 then let
                val () = v1ecs_eq :=
                  INTVECLST1cons (pf_gc, pf_arr | stamp, p, i, v1ecs_eq)
                val () = (vecs := intveclst_make (v1ecs, v1ecs_eq, n))
              in
                ans := intveclst_inspect_gte (vecs, n)
              end else let
                val () = vecs := INTVECLSTnil ()
              in
                intvec_ptr_free (pf_gc, pf_arr | p)
              end
          in
            if ans >= 0 then let
              val ans1 = intveclst_solve (vecs, n)
              val ans2: intBtw (~1, 1) =
                if ans1 >= 0 then begin // continue
                  aux_main (stamp+1, v1ecs, v1ecs_eq, n, !ics_nxt)
                end else begin
                  ~1 // constradiction has been reached
                end
            in
              fold@ (!ic); fold@ (ics); ans2
            end else let
              val () = intveclst_free vecs
            in
              fold@ (!ic); fold@ (ics); ~1(*solved*)
            end // end of [if]
          end // end of [if]
        end // end of [1(*eq*)]
      | _ (* knd = ~1(*neq*) *) => let
          val @(pf1_gc, pf1_arr | p1) = intvecptr_copy (!ivp, n)
          val () = p1->[0] := pred (p1->[0])
          val ivp1 = intvecptr_make_view_ptr (pf1_gc, pf1_arr | p1)
          val ic1 = ICvec (2(*gte*), ivp1)
          val @(pf2_gc, pf2_arr | p2) = intvecptr_copy (!ivp, n)
          val () = intvec_negate (!p2, n)
          val () = p2->[0] := pred (p2->[0])
          val ivp2 = intvecptr_make_view_ptr (pf2_gc, pf2_arr | p2)
          val ic2 = ICvec (2(*gte*), ivp2)
          val () = begin
            intvecptr_free (!ivp); free@ {n} (!ic)
          end
          val ics1: icstrlst n =
            list_vt_cons (ic1, list_vt_cons (ic2, list_vt_nil ()))
          val ans = aux_main_disj (stamp, v1ecs, v1ecs_eq, n, !ics_nxt, ics1)
        in
          !ic := ICveclst (1(*disj*), ics1); fold@ ics; ans
        end // end of [neq]
      end // end of [ICvec]
    | ICveclst (knd(*conj:0/disj:1*), !ics1) => begin
        if knd = 0 then let // conjunction
          val s1 = $Lst.list_vt_length__boxed (!ics1)
          val () = !ics_nxt := $Lst.list_vt_append (!ics1, !ics_nxt)
          val ans = aux_main (stamp, v1ecs, v1ecs_eq, n, !ics_nxt)
          val () = !ics1 := $Lst.list_vt_prefix (!ics_nxt, s1)
        in
          fold@ (!ic); fold@ (ics); ans
        end else let
          val ans = aux_main_disj (stamp, v1ecs, v1ecs_eq, n, !ics_nxt, !ics1)
        in
          fold@ (!ic); fold@ (ics); ans
        end // end of [if]
      end // end of [ICveclst]
    end // end of [list_cons]
  | list_vt_nil () => begin
      fold@ (ics); 0(*unsolved*)
    end // end of [list_nil]
end // end of [aux_main]
//
and aux_main_disj {s,s1:nat} (
    stamp: int
  , v1ecs: &intveclst1 n
  , v1ecs_eq: &intveclst1 n
  , n: int n
  ,ics: &icstrlst (n, s)
  , ics1: !icstrlst (n, s1)
  ) : intBtw (~1, 1) = begin case+ ics1 of
  | list_vt_cons (!ic1, !ics1_nxt) => let
      val () = v1ecs_eq := INTVECLST1mark v1ecs_eq
      val () = v1ecs := INTVECLST1mark v1ecs
      val () = ics := list_vt_cons (!ic1, ics)
      val ans = aux_main (stamp, v1ecs, v1ecs_eq, n, ics)
      val+ ~list_vt_cons (ic1_v, ics_v) = ics
      val () = (!ic1 := ic1_v; ics := ics_v)
      val () = v1ecs_eq := intveclst1_backtrack v1ecs_eq
      val () = v1ecs := intveclst1_backtrack v1ecs
    in
      if ans >= 0 then begin
        fold@ ics1; 0 (*unsolved*)
      end else let // solved and continue
        val ans = aux_main_disj (stamp, v1ecs, v1ecs_eq, n, ics, !ics1_nxt)
      in
        fold@ ics1; ans (*unsolved*)
      end // end of [if]
    end // end of [list_vt_cons]
  | list_vt_nil () => (fold@ ics1; ~1(*solved*))
end // end [aux_main_disj]
//
var v1ecs_eq: intveclst1 n = INTVECLST1nil ()
var v1ecs: intveclst1 n = INTVECLST1nil ()
val ans = aux_main (0(*stamp*), v1ecs, v1ecs_eq, n, ics)
//
in
  intveclst1_free v1ecs_eq; intveclst1_free v1ecs; ans
end // end of [icstrlst_solve]

(* ****** ****** *)

(* end of [ats_solver_fm.dats] *)
