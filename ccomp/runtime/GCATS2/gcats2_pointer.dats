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
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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

// #include "gcats2_ats.hats"

(* ****** ****** *)

#define ATSOPT_NAMESPACE "gcats2_pointer_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

(*
// implemented in [gcats2.cats]
implement PTR_TOPSEG_GET (p) = let
  val u = uintptr_of_ptr (p) // no-op casting
  val u = u >> (PTR_BOTCHKSEG_SIZE + NBYTE_PER_WORD_LOG)
  val u = __cast (u) where {
    extern castfn __cast (u: uintptr):<> [i:nat] topseg i
  } // end of [val]
in
  u // ...
end // end of [PTR_TOPSEG_GET]
*)

(* ****** ****** *)

(*
// implemented in [gcats2.cats]
implement PTR_BOTSEG_GET (p) = let
  val u = uintptr_of_ptr (p) // no-op casting
  val u = u >> (PTR_CHKSEG_SIZE + NBYTE_PER_WORD_LOG)
  val u = uint_of_uintptr (u)
  val mask = uint_of_int (BOTSEG_TABLESIZE_MASK)
  val i = int_of_uint (u land mask)
  val [i:int] i = int1_of_int (i) // no-op casting
#if (GCATS2_DEBUG > 0) #then
  val () = $effmask_all (assert_errmsg (i >= 0, #LOCATION))
  val () = $effmask_all (assert_errmsg (i < BOTSEG_TABLESIZE, #LOCATION))
#else
  val () = __assert () where {
    extern prfun __assert (): [0 <= i; i < BOTSEG_TABLESIZE] void
  } // end of [val]
#endif // end of [GCATS2_DEBUG > 0]
in
  i // ...
end // end of [PTR_BOTSEG_GET]
*)

(* ****** ****** *)

(*
// implemented in [gcats2.cats]

#assert (CHUNK_WORDSIZE == CHKSEG_TABLESIZE)

implement PTR_CHKSEG_GET (p) = let
  val u = uintptr_of_ptr (p) // no-op casting
  val u = u >> NBYTE_PER_WORD_LOG
  val u = uint_of_uintptr (u)
  val mask = uint_of_int (CHUNK_WORDSIZE_MASK)
  val i = int_of_uint (u land mask)
  val [i:int] i = int1_of_int (i) // no-op casting
#if (GCATS2_DEBUG > 0) #then
  val () = $effmask_all (assert_errmsg (i >= 0, #LOCATION))
  val () = $effmask_all (assert_errmsg (i < BOTSEG_TABLESIZE, #LOCATION))
#else
  val () = __assert () where {
    extern prfun __assert (): [0 <= i; i < CHKSEG_TABLESIZE] void
  } // end of [val]
#endif // end of [GCATS2_DEBUG > 0]
in
  i // ...
end // end of [PTR_CHKSEG_GET]
*)

(* ****** ****** *)

%{

ats_ptr_type
gcats2_ptr_isvalid (
  ats_ptr_type ptr, ats_ptr_type r_nitm
) {
  topseg_t ofs_topseg ;
  int ofs_botseg, ofs_chkseg ;
  size_t itmwsz ;
  botsegtblptr_vt p_botsegtbl ;
  chunkptr_vt p_chunk, *r_p_chunk ;

  if (!ptr) return (chunkptr_vt)0 ; // [ptr] is null
/*
  fprintf (stderr, "gcats2_ptr_isvalid(0): ptr = %p\n", ptr) ;
*/
  if ((uintptr_t)ptr & NBYTE_PER_WORD_MASK)
    return (chunkptr_vt)0 ; // [ptr] is not word-aligned
  // end of [if]
/*
  fprintf (stderr, "gcats2_ptr_isvalid(1): ptr = %p\n", ptr) ;
*/
  ofs_topseg = PTR_TOPSEG_GET(ptr) ;
  p_botsegtbl = // pf_botsegtbl, fpf_topsegtbl
    *(botsegtblptr_vt*)(gcats2_the_topsegtbl_takeout(ofs_topseg)) ;
  if (!p_botsegtbl)
    return (chunkptr_vt)0 ; // botsegtbl for [ptr] is not allocated
  // end of [if]
/*
  fprintf (stderr, "gcats2_ptr_isvalid(2): ptr = %p\n", ptr) ;
*/
  ofs_botseg = PTR_BOTSEG_GET(ptr) ;
  r_p_chunk = (chunkptr_vt*)
    gcats2_botsegtblptr1_takeout(p_botsegtbl, ofs_topseg, ofs_botseg) ;
  // [r_p_chunk] may be null if _WORDSIZE==64
  if (!r_p_chunk) return (chunkptr_vt)0 ; // chunk not allocated
  p_chunk = *r_p_chunk ; // pf_chunk, fpf_botsegtbl    
  if (!p_chunk) return (chunkptr_vt)0 ; // chunk for [ptr] is not allocated
  ofs_chkseg = PTR_CHKSEG_GET(ptr) ; itmwsz = p_chunk->itmwsz ;
/*
  fprintf (stderr, "gcats2_ptr_isvalid(3): ptr = %p\n", ptr) ;
  fprintf (stderr, "gcats2_ptr_isvalid(3): p_chunk = %p\n", p_chunk) ;
  fprintf (stderr, "gcats2_ptr_isvalid(3): ofs_chkseg = %i\n", ofs_chkseg) ;
  fprintf (stderr, "gcats2_ptr_isvalid(3): itmwsz = %lu\n", itmwsz) ;
*/
/*
** as a large chunk is (assumed to be) page-aligned,
** [ofs_chkseg] must be a multiple of itmwsz if [ptr] is valid
** (that is, allocated)
*/
  if (ofs_chkseg % itmwsz) return (chunkptr_vt)0 ; // not item-aligned
  *(int*)r_nitm = ofs_chkseg / itmwsz ; // the item number in the chunk
/*
  fprintf (stderr, "gcats2_ptr_isvalid(4): ptr = %p\n", ptr) ;
  fprintf (stderr, "gcats2_ptr_isvalid(4): *r_nitm = %i\n", *(int*)r_nitm) ;
*/
  return p_chunk ; // pf_chunk, fpf_topsegtbl o fpf_botsegtbl
} /* end of [gcats2_ptr_isvalid] */

%} // end of ...

(* ****** ****** *)

(* end of [gcats2_pointer.dats] *)
