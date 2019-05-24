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
// Time: October 2009

(* ****** ****** *)

%{^
#include "libc/CATS/string.cats" // for [memset]
%}

(* ****** ****** *)

// #include "gcats2_ats.hats"

(* ****** ****** *)

#define ATSOPT_NAMESPACE "gcats2_autmem_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

%{^
static inline
ats_int_type gcats2_log2_ceil (
  ats_size_type n0 // [n0 > 0] is assumed
) {
  int n, c ;
  c = 0 ; n = n0 - 1 ; while (n) { c += 1 ; n >>= 1 ; }
#if (GCATS2_TEST > 0)
  if (n0 > (1 << c) || (c > 0 && n0 <= (1 << (c-1)))) {
    fprintf(stderr, "log2_ceil: n0 = %lu and c = %i\n", (ats_ulint_type)n0, c) ;
    exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_TEST]
  return c ;
} // end of [log2_ceil]
%}

extern
fun log2_ceil {n:pos} (n: size_t n):<> int = "gcats2_log2_ceil"

(* ****** ****** *)

implement autmem_malloc_bsz (bsz) = let
  val bsz = size1_of_size (bsz) // no-op casting
  val wsz = (bsz + NBYTE_PER_WORD_MASK) >> NBYTE_PER_WORD_LOG
  val [n:int] wsz = size1_of_size (wsz) // no-op casting
  prval () = __assert () where {
    extern prfun __assert (): [n > 0] void // since [bsz > 0]
  }
in
  autmem_malloc_wsz (wsz)
end // end of [autmem_malloc_wsz]

implement autmem_calloc_bsz (n, bsz) = let
  val (pf_mul | nbsz) = mul2_size1_size1 (n, bsz)
  prval MULind pf1_mul = pf_mul
  prval () = mul_nat_nat_nat (pf1_mul)
  val ptr = autmem_malloc_bsz (nbsz)
  val _(*ptr*) = __memset (ptr, 0, nbsz) where {
    extern fun __memset (_: ptr, _: int, _: size_t):<> ptr = "atslib_memset"
  } // end of [val]
in
  ptr
end // end of [autmem_calloc_bsz]

(* ****** ****** *)

implement autmem_malloc_wsz (wsz) = let
(*
  val () = $effmask_all begin
    prerr "autmem_malloc_wsz: wsz = "; prerr wsz; prerr_newline ()
  end // end of [val]
*)
//
  #assert (FREEITMLST_ARRAYSIZE == MAX_CLICK_WORDSIZE_LOG + 1)
//
  val itmwsz_log = (
    if wsz > MAX_CLICK_WORDSIZE then ~1 else log2_ceil (wsz)
  ) : int
  val [i:int] itmwsz_log = int1_of_int (itmwsz_log)
(*
  val () = $effmask_all begin
    prerr "autmem_malloc_wsz: itmwsz_log = "; prerr itmwsz_log; prerr_newline ()
  end // end of [val]
*)
  prval () = __assert () where {
    extern prfun __assert (): [~1 <= i; i < FREEITMLST_ARRAYSIZE] void
  }
in
  case+ 0 of
  | _ when itmwsz_log >= 0 => let
      var p_itm: ptr =
        the_freeitmlstarr_get_freeitm (itmwsz_log)
      val () = if (p_itm = null) then let
        val (pf_the_gcmain | ()) = the_gcmain_lock_acquire ()
(*
        val () = $effmask_all (fprint_the_freeitmlstarr (stderr_ref))
*)
        val () = the_freeitmlstarr_replenish (pf_the_gcmain | itmwsz_log) // GC may be triggered
(*
        val () = $effmask_all (fprint_the_freeitmlstarr (stderr_ref))
*)
        val () = the_gcmain_lock_release (pf_the_gcmain | (*none*))
        val () = p_itm := the_freeitmlstarr_get_freeitm (itmwsz_log)
        val () = $effmask_all (
          if (p_itm = null) then let
            val () = begin
              prerr "exit(ATS/GC): GC failed to reclaim more memory for allocation.";
              prerr_newline ()
            end // end of [val]
          in
            exit (1)
          end // end of [if]
        ) // end of [val]
      in
        // nothing
      end // end of [val]
    in
      p_itm // [p_itm] <> null
    end // end of [_ when ...]
  | _ => let // [itmwsz_log = -1] // large chunk
(*
      val () = $effmask_all begin
        prerr ("autmem_malloc_wsz: wsz = "); prerr wsz; prerr_newline ()
      end // end of [val]
*)
      val (pf_the_gcmain | ()) = the_gcmain_lock_acquire ()
      prval (pf, fpf) = the_totwsz_v_takeout (pf_the_gcmain)
      val p_chunk = chunk_make_large (wsz)
      val () = the_totwsz_add_wsz (pf | wsz)
      val (pf_chunk | p) = chunkptr_unfold p_chunk
      val p_data = chunk_data_get (!p)
      val _(*ptr*) = chunkptr_fold (pf_chunk | p_chunk)
      prval () = pf_the_gcmain := fpf (pf)
      prval (pf, fpf) = the_topsegtbl_v_takeout (pf_the_gcmain)
      val _(*err*) = the_topsegtbl_insert_chunkptr (pf | p_chunk)
      prval () = pf_the_gcmain := fpf (pf)
      val () = the_gcmain_lock_release (pf_the_gcmain | (*none*))
(*
      val () = $effmask_all begin
        prerr ("autmem_malloc_wsz: p_chunk = "); prerr p; prerr_newline ()
      end // end of [val]
      val () = $effmask_all begin
        prerr ("autmem_malloc_wsz: p_data = "); prerr p_data; prerr_newline ()
      end // end of [val]
*)
    in
      p_data
    end // end of [_]
end // end of [autmem_malloc_wsz]

(* ****** ****** *)

%{$

ats_void_type
gcats2_autmem_free (
  ats_ptr_type p_itm // [p_itm] is assumed to be valid
) {
  int itmwsz_log ;
  chunk_vt *p_chunk ; int ofs_nitm ;
  freeitmlst_vt *p_itmlst ;
//
  p_chunk = (chunk_vt*)gcats2_ptr_isvalid(p_itm, &ofs_nitm) ;
//
#if (GCATS2_DEBUG > 0)
  if (!p_chunk) {
    fprintf(stderr, "INTERNAL ERROR") ;
    fprintf(stderr, ": exit(ATS/GC): gcats2_autmem_free: p_itm = %p\n", p_itm) ;
    exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG]
  itmwsz_log = ((chunk_vt*)p_chunk)->itmwsz_log ;
/*
    fprintf(stderr, "gcats2_autmem_free: the_totwsz = %lu\n", the_totwsz) ;
    fprintf(stderr, "gcats2_autmem_free: p_chunk->itmwsz = %lu\n", p_chunk->itmwsz) ;
    fprintf(stderr, "gcats2_autmem_free: itmwsz_log = %i\n", itmwsz_log) ;
*/
  if (itmwsz_log >= 0) {
    p_itmlst = &the_freeitmlstarr[itmwsz_log] ;
    *(freeitmlst_vt*)p_itm = *p_itmlst ; *p_itmlst = (freeitmlst_vt)p_itm ;
  } else { // itmwsz_log = -1 // itmtot = 1
    the_totwsz -= p_chunk->itmwsz ;
    gcats2_the_topsegtbl_remove_chunkptr(p_chunk->chunk_data) ;
    gcats2_chunk_free_large(p_chunk) ; // [gcats2_munmap_ext] is called
  } // end of [if]
//
  return ;
} // end of [gcats2_autmem_free]

ats_ptr_type
gcats2_autmem_realloc_bsz (
  ats_ptr_type p_itm, ats_size_type bsz // [p_itm] is assumed to be valid
) {
  size_t itmwsz, itmbsz ;
  chunk_vt *p_chunk ; int itmwsz_log, ofs_nitm ;
  freeitmptr_vt p_itm_new ;
  freeitmlst_vt *p_itmlst ;
//
  p_chunk = (chunk_vt*)gcats2_ptr_isvalid(p_itm, &ofs_nitm) ;
//
#if (GCATS2_DEBUG > 0)
  if (!p_chunk) {
    fprintf(stderr, "INTERNAL ERROR") ;
    fprintf(stderr, ": exit(ATS/GC): gcats2_autmem_free: p_itm = %p\n", p_itm) ;
    exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG]
//
  itmwsz = ((chunk_vt*)p_chunk)->itmwsz ;
  itmbsz = (itmwsz << NBYTE_PER_WORD_LOG) ;
  itmwsz_log = ((chunk_vt*)p_chunk)->itmwsz_log ;
//
  if (itmwsz_log >= 0) {
    if (bsz <= itmbsz && itmbsz / 2 < bsz) return p_itm ;
  } // end of [if]
//
  if (bsz) {
    p_itm_new =
      gcats2_autmem_malloc_bsz (bsz) ;
    if (bsz <= itmbsz)
      memcpy (p_itm_new, p_itm, bsz) ;
    else
      memcpy (p_itm_new, p_itm, itmbsz) ;
    // end of [if]
  } else {
    p_itm_new = (freeitmptr_vt)0 ;
  } // end of [if]
/*
  fprintf(stderr, "gcats2_autmem_realloc_bsz: bsz = %lu\n", bsz) ;
  fprintf(stderr, "gcats2_autmem_realloc_bsz: itmbsz = %lu\n", itmbsz) ;
  fprintf(stderr, "gcats2_autmem_realloc_bsz: itmwsz_log = %i\n", itmwsz_log) ;
*/
  if (itmwsz_log >= 0) {
    p_itmlst = &the_freeitmlstarr[itmwsz_log] ;
    *(freeitmlst_vt*)p_itm = *p_itmlst ; *p_itmlst = (freeitmlst_vt)p_itm ;
  } else { // itmwsz_log = -1 // itmtot = 1
    the_totwsz -= p_chunk->itmwsz ;
    gcats2_the_topsegtbl_remove_chunkptr(p_chunk->chunk_data) ;
    gcats2_chunk_free_large(p_chunk) ; // [gcats2_munmap_ext] is called
  } // end of [if]
//
  return p_itm_new ;
} // end of [gcats2_autmem_realloc_bsz]

%} // end of [%{$]

(* ****** ****** *)

(* end of [gcats2_autmem.dats] *)
