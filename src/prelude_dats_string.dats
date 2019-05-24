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

#define ATS_DYNLOADFLAG 0 // no need for dynamic loading

(* ****** ****** *)

// implement string_empty = "" // this requires dynamic loading

(* ****** ****** *)

%{^

ATSinline()
ats_ptr_type
atsopt_stringlst_concat_string_alloc
  (const ats_size_type n) {
  char *p ;
  p = ATS_MALLOC(n+1); p[n] = '\000'; return p ;
} // end of [atsopt_stringlst_string_alloc]

%} // end of [%{^]

(* ****** ****** *)

implement
stringlst_concat (ss) = let
  val n0 = aux (ss, size1_of_int1 0) where {
    fun aux {k:nat} .<k>. (
      ss: list (string, k), n: size_t
    ) :<> size_t = case+ ss of
      | list_cons (s, ss) => aux (ss, n + string0_length s)
      | list_nil () => n
    // end of [aux]
  } // end of [val n0]
  val n0 = size1_of_size (n0)
  fun loop1 {m0,n0,i0,n,i:nat | i0 <= n0; i <= n} .<n0-i0>. (
    s0: &strbuf (m0, n0)
  , n0: size_t n0, i0: size_t i0, s: string n, i: size_t i
  ) :<> [i0: nat | i0 <= n0] size_t i0 = begin
    if string_is_atend (s, i) then i0 else let
      val c = $effmask_ref (s[i])
    in
      if i0 < n0 then (s0[i0] := c; loop1 (s0, n0, i0+1, s, i+1)) else i0
    end // end of [if]
  end // end of [loop1]
  fun loop2 {m0,n0,i0,k:nat | i0 <= n0} .<k>. (
    s0: &strbuf (m0, n0)
  , n0: size_t n0, i0: size_t i0, ss: list (string, k)
  ) :<> void = begin case+ ss of
    | list_cons (s, ss) => let
        val s = string1_of_string s; val i0 = loop1 (s0, n0, i0, s, 0)
      in
        loop2 (s0, n0, i0, ss)
      end // end of [list_cons]
    | list_nil () => () // loop exists
  end // end of [loop2]
  val (pf_gc, pf_sb | p_sb) =
    string_alloc (n0) where {
    extern fun string_alloc {n:nat} (n: size_t n)
      :<> [l:addr] (freebyte_gc_v (n+1, l), strbuf (n+1, n) @ l | ptr l)
      = "atsopt_stringlst_concat_string_alloc"
  } // end of [val]
  val () = loop2 (!p_sb, n0, 0, ss)
in
  strptr_of_strbuf @(pf_gc, pf_sb | p_sb)
end // end of [stringlst_concat]

(* ****** ****** *)

%{$
//
// a commonly used simple hash function
//
ats_ulint_type
atspre_string_hash_33
  (ats_ptr_type s0) {
  unsigned long int hash_val ; unsigned char *s; int c;
  hash_val = 31415926UL ; // randomly chosen
  s = (unsigned char*)s0 ; while (1) {
    c = *s ;
    if (!c) return hash_val ;
    hash_val = ((hash_val << 5) + hash_val) + c ;
    s += 1 ;
  }
} /* end of [atspre_string_hash] */

%} // end of [%{$]

(* ****** ****** *)

%{$

ats_ptr_type
atspre_string_make_substring
(
  ats_ptr_type src0
, ats_size_type st, ats_size_type ln
) {
  char *des, *src ;
  des = ATS_MALLOC(ln+1) ;
  src = ((char*)src0) + st ;
  memcpy(des, src, ln) ; des[ln] = '\000' ;
  return des ;
} /* atspre_string_make_substring */

%} // end of [%{$]

(* ****** ****** *)

(* end of [prelude_dats_string.dats] *)
