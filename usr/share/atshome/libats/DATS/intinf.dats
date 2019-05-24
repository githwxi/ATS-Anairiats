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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// infinite precision integers based on the gmp package

(* ****** ****** *)

%{^
#include "libc/CATS/gmp.cats"
%} // end of [%{^]

(* ****** ****** *)

staload "libc/SATS/gmp.sats"
staload "libats/SATS/intinf.sats"

(* ****** ****** *)

assume intinf (i: int) = // HX: [i] is a fake
  [l:addr] (free_gc_v (mpz_vt?, l), mpz_vt @ l | ptr l)
// end of [intinf]

(* ****** ****** *)

implement
intinf_make_int {i} (i) = let
  val (pf_gc, pf_at | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init_set_int (!p, i)
in
  @(pf_gc, pf_at | p)
end // end of [intinf_make_int]

implement
intinf_make_lint (i) = let
  val @(pf_gc, pf_at | p) =
    ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val i = lint_of_lint1 (i) where { 
    extern castfn lint_of_lint1 {i:int} (x: lint i):<> lint
  } // end of [val]
  val () = mpz_init_set_lint (!p, i)
in
  @(pf_gc, pf_at | p)
end // end of [intinf_make_lint]

implement
intinf_make_llint (i) = let
  val @(pf_gc, pf_at | p) =
    ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val i = llint_of_llint1 (i) where {
    extern castfn llint_of_llint1 {i:int} (x: llint i):<> llint
  } // end of [val]
  val i = double_of_llint (i)
  val () = mpz_init_set_double (!p, i)
in
  @(pf_gc, pf_at | p)
end // end of [intinf_make_llint]

implement
intinf_make_double (d) = let
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init_set_double (!p, d)
in
  #[0 | (pfgc, pfat | p)] // HX: [0] is just a place holder
end // end of [intinf_make_double]

implement
intinf_make_string (rep) = let
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init_set_str_exn (!p, rep, 10(*base*))
in
  #[0 | (pfgc, pfat | p)] // HX: [0] is just a place holder
end // end of [intinf_make_double]

(* ****** ****** *)

implement
intinf_free @(pf_gc, pf_at | p) =
  (mpz_clear (!p); ptr_free {mpz_vt?} (pf_gc, pf_at | p))
// end of [intinfptr_free]

(* ****** ****** *)

implement
fprint0_intinf
  (out, intinf) = fprint0_intinf_base (out, 10, intinf)
// end of [fprint0_intinf]
implement
fprint1_intinf
  (pf | fil, intinf) = fprint1_intinf_base (pf | fil, 10, intinf)
// end of [fprint1_intinf]

implement print_intinf (intinf) = print_mac (fprint1_intinf, intinf)

(* ****** ****** *)

implement
fprint0_intinf_base
  (out, base, intinf) = let
  val [l:addr]
    (pffil | p) = __cast (out) where {
    extern castfn __cast
      (out: FILEref): [l:addr] (FILE(w) @ l | ptr l)
    // end of [extern]
  } // end of [val]
  val () = fprint1_intinf_base (file_mode_lte_w_w | !p, base, intinf)
  prval () = __free (pffil) where {
    extern praxi __free (pf: FILE(w) @ l): void
  } // end of [prval]
in
  (*nothing*)
end // end of [fprint0_intinf_base]

implement
fprint1_intinf_base
  (pf | fil, base, intinf) = () where {
  prval pfat = intinf.1
  val n = mpz_out_str (pf | fil, base, !(intinf.2))
  prval () = intinf.1 := pfat
  val () = assert_errmsg (n > 0, "exit(ATS): [fprint_intinf_base] failed.\n")
} // end of [fprint1_intinf_base]

implement
print_intinf_base (base, intinf) = let
  val (pf_stdout | p_stdout) = stdout_get ()
  val () = fprint1_intinf_base
    (file_mode_lte_w_w | !p_stdout, base, intinf)
  val () = stdout_view_set (pf_stdout | (*none*))
in
  // empty
end // end of [print_intinf_base]

(* ****** ****** *)

implement
pred_intinf (intinf) = let
  prval pf = intinf.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_sub (!p, !(intinf.2), 1)
  prval () = intinf.1 := pf
in
  @(pfgc, pfat | p)
end // end of [pred_intinf]

implement
succ_intinf (intinf) = let
  prval pf = intinf.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_add (!p, !(intinf.2), 1)
  prval () = intinf.1 := pf
in
  @(pfgc, pfat | p)
end // end of [succ_intinf]

(* ****** ****** *)

implement
add_intinf_int (intinf, i) = let
  prval pf = intinf.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_add (!p, !(intinf.2), i)
  prval () = intinf.1 := pf
in
  @(pfgc, pfat | p)
end // end of [add_intinf_int]

implement
add_intinf_intinf (intinf1, intinf2) = let
  prval pf1 = intinf1.1
  prval pf2 = intinf2.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_add (!p, !(intinf1.2), !(intinf2.2))
  prval () = intinf1.1 := pf1
  prval () = intinf2.1 := pf2
in
  @(pfgc, pfat | p)
end // end of [add_intinf_intinf]

(* ****** ****** *)

implement
sub_intinf_int (intinf, i) = let
  prval pf = intinf.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_sub (!p, !(intinf.2), i)
  prval () = intinf.1 := pf
in
  @(pfgc, pfat | p)
end // end of [sub_intinf_int]

implement
sub_intinf_intinf (intinf1, intinf2) = let
  prval pf1 = intinf1.1
  prval pf2 = intinf2.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_sub (!p, !(intinf1.2), !(intinf2.2))
  prval () = intinf1.1 := pf1
  prval () = intinf2.1 := pf2
in
  @(pfgc, pfat | p)
end // end of [sub_intinf_intinf]

(* ****** ****** *)

implement
mul_int_intinf {m,n} (int, intinf) = let
  prval pfmul = mul_make {m,n} ()
  prval pf = intinf.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_mul (!p, !(intinf.2), int)
  prval () = intinf.1 := pf
in
  @(pfmul | @(pfgc, pfat | p))
end // end of [mul_int_intinf]

implement
mul_intinf_int {m,n} (intinf, int) = let
  prval pfmul = mul_make {m,n} ()
  prval pf = intinf.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_mul (!p, !(intinf.2), int)
  prval () = intinf.1 := pf
in
  @(pfmul | @(pfgc, pfat | p))
end // end of [mul_intinf_int]

implement
mul_intinf_intinf {m,n} (intinf1, intinf2) = let
  prval pfmul = mul_make {m,n} ()
  prval pf1 = intinf1.1
  prval pf2 = intinf2.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p); val () = mpz_mul (!p, !(intinf1.2), !(intinf2.2))
  prval () = intinf1.1 := pf1
  prval () = intinf2.1 := pf2
in
  @(pfmul | @(pfgc, pfat | p))
end // end of [mul_intinf_intinf]

(* ****** ****** *)

implement
square_intinf {n} (intinf) = let
  prval pf = intinf.1
  prval pfmul = mul_make {n,n} ()
  val @(pfgc, pfat | p) =
    ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init_set (!p, !(intinf.2)); val () = mpz_mul (!p, !(intinf.2))
  prval () = intinf.1 := pf
in
  @(pfmul | @(pfgc, pfat | p))
end // end of [square_intinf]

(* ****** ****** *)

implement
fdiv_intinf_int {m,n} (intinf, i) = let
  prval [q,r:int] pfmul = lemma () where {
    extern prfun lemma () : [q,r:int | 0 <= r; r < n] MUL (q, n, m-r)
  } // end of [prval]
  prval pf = intinf.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  val ui = ulint_of_int i; val _(*remainder*) = mpz_fdiv_q (!p, !(intinf.2), ui)
  prval () = intinf.1 := pf
in
  #[q,r | @(pfmul | @(pfgc, pfat | p))]
end // end of [fdiv_intinf_int]

implement
fmod_intinf_int {m,n} (intinf, i) = let
  prval [q,r:int] pfmul =
    div_lemma {m,n} () where {
    extern praxi div_lemma {m,n:int | n > 0} ()
      : [q,r:int | 0 <= r; r < n] MUL (q, n, m-r)
  } // end of [prval]
  prval pf = intinf.1
  val @(pfgc, pfat | p) = ptr_alloc_tsz {mpz_vt} (sizeof<mpz_vt>)
  val () = mpz_init (!p)
  val ui = ulint_of_int i; val _(*remainder*) = mpz_mod (!p, !(intinf.2), ui)
  prval () = intinf.1 := pf
  val r = mpz_get_int (!p)
  val [r1:int] r = int1_of_int r
  prval () = __assert () where { extern prfun __assert (): [r==r1] void }
  val () = intinf_free @(pfgc, pfat | p)
in
  #[q,r | @(pfmul | r)]
end // end of [fmod_intinf_int]

(* ****** ****** *)

(* end of [intinf.dats] *)
