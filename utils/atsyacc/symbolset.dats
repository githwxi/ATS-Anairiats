(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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
**
*)

(* ****** ****** *)

// February 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "symbol.sats"

(* ****** ****** *)

%{^

#if (__WORDSIZE == 32)

#define WORDSIZE 32
#define WORDSIZE_LOG 5

#endif

#if (__WORDSIZE == 64)

#define WORDSIZE 64
#define WORDSIZE_LOG 6

#endif

#ifndef WORDSIZE
#error "[WORDSIZE] is undefined!"
#endif

%}

(* ****** ****** *)

typedef bitvec (n:int) = @[uintptr][n]

(* ****** ****** *)

// vec1 <- vec1 union vec2

extern fun bitvec_union {n:nat} 
  (vec1: &bitvec n, vec2: &bitvec n, n: int n): void
  = "atsyacc_bitvec_union"

implement bitvec_union (vec1, vec2, n) = let
  var i: Nat // uninitialized
in
  for (i := 0; i < n; i := i+1) vec1.[i] := (vec1.[i] lor vec2.[i])
end // end of [bitvec_union]

extern fun bitvec_union_flag {n:nat} 
  (vec1: &bitvec n, vec2: &bitvec n, n: int n, flag: &int): void
  = "atsyacc_bitvec_union_flag"

implement bitvec_union_flag (vec1, vec2, n, flag) = let
  var i: Nat // uninitialized
in
  for (i := 0; i < n; i := i+1) let
    val x0 = vec1.[i]; val x1 = x0 lor vec2.[i]
  in
    if x0 <> x1 then (flag := flag + 1; vec1.[i] := x1)
  end // end [for]
end (* end of [bitvec_union_flag] *)

(* ****** ****** *)

implement print_symbolset (x) = print_mac (fprint_symbolset, x)
implement prerr_symbolset (x) = prerr_mac (fprint_symbolset, x)

(* ****** ****** *)

%{$

// totol number of terminals
static ats_int_type the_termtot = 0 ;
static ats_int_type the_bitvecsz = 0 ;

extern ats_int_type atsyacc_symbol_term_total_get () ;

ats_void_type
atsyacc_the_bitvecsz_set (ats_int_type n) {
  the_termtot = n ;
  the_bitvecsz = (n + WORDSIZE - 1) >> WORDSIZE_LOG ;
  fprintf (stdout, "the_bitvecsz = %i\n", the_bitvecsz) ;
  return ;
}

ats_void_type
atsyacc_bitvec_add
  (ats_ref_type vec, ats_int_type ind) {
  int i0 , i1 ;
/*
  fprintf (stderr, "atsyacc_bitvec_add: ind = %i\n", ind) ;
*/
  i0 = ind >> WORDSIZE_LOG ;
  i1 = ind & (WORDSIZE - 1) ;
  ((uintptr_t*)vec)[i0] |= (1 << i1) ;
  return ;
}

ats_bool_type
atsyacc_bitvec_ismem
  (ats_ref_type vec, ats_int_type ind) {
  int i0 = ind >> WORDSIZE_LOG ;
  int i1 = ind & (WORDSIZE - 1) ;
  return ((uintptr_t*)vec)[i0] & (1 << i1) ;
}

//

ats_ptr_type _atsyacc_symbolset_nil = 0 ;

ats_ptr_type
atsyacc_symbolset_nil () {
  int n ; ats_ptr_type p ;
/*
  fprintf (stdout,
    "atsyacc_symbolset_nil: the_bitvecsz = %i\n", the_bitvecsz
  ) ;
*/
  p = ATS_CALLOC (the_bitvecsz, sizeof (uintptr_t)); return p ;
}

ats_ptr_type
atsyacc_symbolset_sing (ats_ptr_type sym) {
  ats_ptr_type set ;
  ats_int_type ind ;
  ind = atsyacc_symbol_index_get (sym) ;
/*
  fprintf (stdout, "atsyacc_symbolset_sing: ind = %i\n", ind) ;
*/
  set = atsyacc_symbolset_nil () ; atsyacc_bitvec_add (set, ind) ;
  return set ;
}

ats_void_type
atsyacc_symbolset_add
  (ats_ptr_type set, ats_ptr_type sym) {
  ats_int_type ind ;
  ind = atsyacc_symbol_index_get (sym) ;
  atsyacc_bitvec_add (set, ind) ; return ;
}

ats_ptr_type
atsyacc_symbolset_union
  (ats_ptr_type set1, ats_ptr_type set2) {
  atsyacc_bitvec_union (set1, set2, the_bitvecsz) ;
  return set1 ;
}

ats_ptr_type
atsyacc_symbolset_union_flag
  (ats_ptr_type set1, ats_ptr_type set2, ats_ref_type flag) {
  atsyacc_bitvec_union_flag (set1, set2, the_bitvecsz, flag) ;
  return set1 ;
}

/* ****** ****** */

extern
ats_ptr_type atsyacc_the_alltermarr_get (ats_int_type ind) ;

ats_void_type
atsyacc_fprint_symbolset (ats_ptr_type out, ats_ptr_type set) {
  ats_ptr_type sym ;
  ats_int_type ind ;
  int i = 0 ;
  
  for (ind = 0 ; ind < the_termtot ; ind += 1) {
    if (atsyacc_bitvec_ismem (set, ind)) {
      if (i > 0) fprintf ((FILE*)out, ", ") ; i += 1 ;
      sym = atsyacc_the_alltermarr_get (ind) ;
      atsyacc_fprint_symbol ((FILE*)out, sym);
    }
  } /* end of [for] */
}

%}

(* ****** ****** *)

(* end of [symbolset.dats] *)
