(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October, 2009

(* ****** ****** *)

// #include "gcats2_ats.hats"

(* ****** ****** *)

#define ATSOPT_NAMESPACE "gcats2_manmem_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

implement manmem_malloc_bsz (bsz) = let
  val (pf_mem | p_mem) =
    manmem_create (bsz) where {
    extern fun manmem_create {n:pos}
      (bsz: size_t n):<> [l:addr] (manmem_vt @ l | ptr l)
      = "gcats2_manmem_create"
  } // end of [val]
  val p_data = manmem_data_get (!p_mem)
  val (pf_lst | ()) = the_manmemlst_lock_acquire ()
  val () = the_manmemlst_insert (pf_lst, pf_mem | p_mem)
  val () = the_manmemlst_lock_release (pf_lst | (*none*))
in
  p_data
end // end of [manmem_malloc_bsz]

implement manmem_calloc_bsz (n, bsz) = let
  val (pf_mul | nbsz) = mul2_size1_size1 (n, bsz)
  prval MULind pf1_mul = pf_mul
  prval () = mul_nat_nat_nat (pf1_mul)
  val ptr = manmem_malloc_bsz (nbsz)
  val _(*ptr*) = __memset (ptr, 0, nbsz) where {
    extern fun __memset (_: ptr, _: int, _: size_t):<> ptr = "atslib_memset"
  } // end of [val]
in
  ptr
end // end of [manmem_calloc_bsz]

implement manmem_free (p_data) = let
  val (pf_lst | ()) = the_manmemlst_lock_acquire ()
  val (pf_mem | p_mem) = the_manmemlst_remove (pf_lst | p_data)
  val () = the_manmemlst_lock_release (pf_lst | (*none*))
  val () = manmem_destroy (pf_mem | p_mem) where {
    extern fun manmem_destroy {l:addr} (pf: manmem_vt @ l | p: ptr l):<> void
      = "gcats2_manmem_destroy"
  } // end fo [val]
in
  // nothing
end // end of [manmem_free]

implement manmem_realloc_bsz
  (p_data, bsz) = let val bsz = size1_of_size (bsz)
in
  if bsz > 0 then let
    val (pf_lst | ()) = the_manmemlst_lock_acquire ()
    val (pf_mem | p_mem) = the_manmemlst_remove (pf_lst | p_data)
    val p_mem_new = manmem_recreate (pf_mem | p_mem, bsz) where {
      extern fun manmem_recreate {n:pos} {l:addr}
        (pf: !manmem_vt @ l >> manmem_vt @ l_new | p: ptr l, bsz: size_t n)
        :<> #[l_new:addr] ptr l_new
        = "gcats2_manmem_recreate"
    } // end of [val]
    val p_data = manmem_data_get (!p_mem_new)
    val () = the_manmemlst_insert (pf_lst, pf_mem | p_mem_new)
    val () = the_manmemlst_lock_release (pf_lst | (*none*))
  in
    p_data
  end else let
    val () = manmem_free (p_data) in null
  end // end of [if]
end // end of [manmem_realloc_bsz]

(* ****** ****** *)

%{^

ats_ptr_type
gcats2_manmem_data_get (
  ats_ptr_type p_manmem // p_manmem != NULL
) {
  return ((manmem_vt*)p_manmem)->manmem_data ;
} /* end of [gcats2_manmem_data_get] */

/* ****** ****** */

ats_ptr_type
gcats2_manmem_create (
  ats_size_type bsz
) {
  manmem_vt *p_manmem ;
  p_manmem = gcats2_malloc_ext(sizeof(manmem_vt) + bsz) ;
  p_manmem->manmem_wsz = (bsz + NBYTE_PER_WORD_MASK) >> NBYTE_PER_WORD_LOG ;
  return (ats_ptr_type)p_manmem ;
} /* end of [gcats2_manmem_create] */

ats_void_type
gcats2_manmem_destroy (
  ats_ptr_type p_manmem
) {
  gcats2_free_ext(p_manmem) ; return ;
} /* end of [gcats2_manmem_destroy] */

ats_ptr_type
gcats2_manmem_recreate (
  ats_ptr_type p_manmem, ats_size_type bsz
) {
  p_manmem = gcats2_realloc_ext(p_manmem, sizeof(manmem_vt) + bsz) ;
  ((manmem_vt*)p_manmem)->manmem_wsz = (bsz + NBYTE_PER_WORD_MASK) >> NBYTE_PER_WORD_LOG ;
  return p_manmem ;
} /* end of [gcats2_manmem_create] */

/* ****** ****** */

ats_int_type
gcats2_the_manmemlst_length (
  // there is no argument for this function
) {
  int n ; manmemlst_vt p ;
  n = 0 ; p = the_manmemlst ; while (p) { n += 1 ; p = p->next ; }
  return n ;
} /* end of [gcats2_the_manmemlst_length] */

/* ****** ****** */

ats_void_type
gcats2_the_manmemlst_insert (
  ats_ptr_type p_mem // [p_mem] != NULL
) {
  // inserted as the head of the_manmemlst
  ((manmemlst_vt)p_mem)->prev = (manmemlst_vt)0 ;
  ((manmemlst_vt)p_mem)->next = the_manmemlst ;
  if (the_manmemlst) the_manmemlst->prev = p_mem ;
  the_manmemlst = p_mem ;
  return ;
} /* end of [gcats2_the_manmemlst_insert] */

ats_ptr_type
gcats2_the_manmemlst_remove (
  ats_ptr_type p_data // [p_data] points to the middle of ...
) {
  manmemlst_vt p =
    (manmemlst_vt)((byte*)p_data - sizeof(manmem_vt)) ;
  manmemlst_vt p_prev, p_next ;
  p_prev = ((manmemlst_vt)p)->prev ; // p != NULL
  p_next = ((manmemlst_vt)p)->next ; // p != NULL
  if (p_prev)
    p_prev->next = p_next ;
  else /* p: first one in the_manmemlst */
    the_manmemlst = p_next ;
  // end of [if]
  if (p_next) p_next->prev = p_prev ;
  return p ;
} /* end of [gcats2_the_manmemlst_remove] */

/* ****** ****** */

extern
ats_int_type gcats2_ptrsize_mark (ats_ptr_type ptr, ats_size_type wsz) ;

ats_int_type
gcats2_the_manmemlst_mark (
  // there is no argument for this function
) {
  manmemlst_vt p ; int overflow ;
  p = the_manmemlst ; overflow = 0 ;
// /*
  fprintf(stderr, "gcats2_the_manmemlst_mark: starts\n") ;
// */
  while (p) {
    overflow += gcats2_ptrsize_mark(p->manmem_data, p->manmem_wsz) ; p = p->next ;
  } // end of [while]
// /*
  fprintf(stderr, "gcats2_the_manmemlst_mark: finishes: overflow = %i\n", overflow) ;
// */
  return overflow ;
} /* end of [gcats2_the_manmemlst_mark] */

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_manmem.dats] *)
