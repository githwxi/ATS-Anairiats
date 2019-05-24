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
// Time: October, 2009

(* ****** ****** *)

// #include "gcats2_ats.hats"

(* ****** ****** *)

#define ATSOPT_NAMESPACE "gcats2_chunk_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

implement the_chunkpagelst_remove
  (pf | (*none*)) = let
  #define NBATCH 1024 // it is arbitrarily chosen!
  val (pfopt | p) = the_chunkpagelst_remove_opt (pf | (*none*))
  prval () = ptr_is_gtez (p)
in
  if (p > null) then let
    prval Some_v pf = pfopt in (pf | p)
  end else let
    prval None_v () = pfopt
    val n = the_chunkpagelst_replenish (pf | NBATCH)
  in
    case+ 0 of
    | _ when n >= 0 => the_chunkpagelst_remove (pf | (*none*))
    | _ => $effmask_all (let
        val () = prerr "exit(ATS/GCATS2)"
        val () = prerr ": the_chunkpagelst_remove: mmap failed"
        val () = prerr_newline ()
      in
        exit (1)
      end) // end of [_]
  end (* end of [if] *)
end // end of [...]

(* ****** ****** *)

implement the_topsegtbl_clear_mrkbits
  (pf_tbl | (*none*)) = let
  prval pf = unit_v ()
  val f = lam {l:agz} (
      pf_tbl: !the_topsegtbl_v, pf: !unit_v | p_chunk: !chunkptr_vt l, env: !ptr
    ) : void =<fun> let
    val (pf_chunk | p) = chunkptr_unfold (p_chunk)
    val () = chunk_mrkbits_clear (!p)
    val _(*ptr*) = chunkptr_fold (pf_chunk | p_chunk)
  in
    // nothing
  end
  val () = the_topsegtbl_foreach_chunkptr {unit_v} {ptr} (pf_tbl, pf | f, null)
  prval unit_v () = pf
in
  // nothing
end // end of [the_topsegtbl_clear_mrkbits]

(* ****** ****** *)

%{^

ats_void_type
gcats2_fprint_chunk (
  ats_ptr_type out, ats_ptr_type p_chunk
) {
  int i, itmtot ;
  if (!p_chunk) {
    fprintf((FILE*)out, "(chunknil)\n") ; return ;
  }
  fprintf((FILE*)out, "itmwsz = %i\n", ((chunk_vt*)p_chunk)->itmwsz) ;
  fprintf((FILE*)out, "itmwsz_log = %i\n", ((chunk_vt*)p_chunk)->itmwsz_log) ;
  itmtot = ((chunk_vt*)p_chunk)->itmtot ;
  fprintf((FILE*)out, "itmtot = %i\n", itmtot) ;
  fprintf((FILE*)out, "mrkcnt = %i\n", ((chunk_vt*)p_chunk)->mrkcnt) ;
  fprintf((FILE*)out, "chunk_data = %p\n", ((chunk_vt*)p_chunk)->chunk_data) ;

  fprintf((FILE*)out, "mrkbits = ") ; 
  for (i = 0; i < itmtot; i += 1) {
    fprintf((FILE*)out, "%i", MARKBIT_GET(((chunk_vt*)p_chunk)->mrkbits, i)) ;
  }
  fprintf((FILE*)out, "\n") ; 
  fprintf((FILE*)out, "##### end of a chunk #######\n") ;
  return ;
} /* end of [gcats2_fprint_chunk] */

ats_void_type
gcats2_fprint_the_topsegtbl
  (ats_ptr_type out) {
  int i, j ;
  botsegtblptr_vt p_botsegtbl ;
  chunkptr_vt p_chunk ;

#if (__WORDSIZE == 32)
  for (i = 0; i < TOPSEG_TABLESIZE; i += 1) {
    p_botsegtbl = the_topsegtbl[i] ;
    if (p_botsegtbl) {
      for (j = 0; j < BOTSEG_TABLESIZE; j += 1) {
        p_chunk = p_botsegtbl->headers[j] ;
        if (p_chunk) gcats2_fprint_chunk (out, p_chunk) ;
      } // end of [for]
      fprintf((FILE*)out, "##### end of a botsegtbl #######\n") ;
    } // end of [if]
  } // end of [for]
#endif // end of ...

#if (__WORDSIZE == 64)
  for (i = 0; i < TOPSEG_HASHTABLESIZE; i += 1) {
    p_botsegtbl = the_topsegtbl[i] ;
    while (p_botsegtbl) {
      for (j = 0; j < BOTSEG_TABLESIZE; j += 1) {
        p_chunk = p_botsegtbl->headers[j] ;
        if (p_chunk) gcats2_fprint_chunk (out, p_chunk) ;
      } // end of [for]
      fprintf((FILE*)out, "##### end of a botsegtbl #######\n") ;
      p_botsegtbl = p_botsegtbl->hashnext ;
    } // end of [while]
  } // end of [for]
#endif // end of ...

  return ;
} // end of [gcats2_fprint_the_topsegtbl]

%} // end of [%{^]

(* ****** ****** *)

%{^

ats_void_type
gcats2_the_totwsz_add_wsz (
  ats_size_type wsz
) {
  the_totwsz += wsz ; return ;
} // end of [gcats2_the_totwsz_add_wsz]

ats_void_type
gcats2_the_totwsz_add_chunk (
  ats_ptr_type p_chunk, ats_int_type itmwsz_log // p_chunk != NULL
) {
  int itmtot, mrkcnt ;
  itmtot = ((chunk_vt*)p_chunk)->itmtot ;
  mrkcnt = ((chunk_vt*)p_chunk)->mrkcnt ;
  the_totwsz += (itmtot - mrkcnt) << itmwsz_log ;
  return ;
} // end of [gcats2_the_totwsz_add_chunk]

ats_void_type
gcats2_the_freeitmlstarr_add_chunk (
  ats_ptr_type p_chunk // p_chunk != NULL
, ats_int_type itmwsz_log // itmwsz_log < FREEITMLST_ARRAYSIZE
) {
  int i, itmwsz, itmtot ;
  freeitmptr_vt *p_data ; byte *mrkbits ;
  freeitmlst_vt xs ;
//
  itmwsz = ((chunk_vt*)p_chunk)->itmwsz ;
  itmtot = ((chunk_vt*)p_chunk)->itmtot ;
  p_data = ((chunk_vt*)p_chunk)->chunk_data ;
/*
  fprintf(stderr, "gcats2_the_freeitmlstarr_add_chunk: itmwsz = %i\n", itmwsz) ;
  fprintf(stderr, "gcats2_the_freeitmlstarr_add_chunk: itmwsz_log = %i\n", itmwsz_log) ;
  fprintf(stderr, "gcats2_the_freeitmlstarr_add_chunk: itmtot = %i\n", itmtot) ;
  fprintf(stderr, "gcats2_the_freeitmlstarr_add_chunk: p_data = %p\n", p_data) ;
*/
  xs = the_freeitmlstarr[itmwsz_log] ;
//
  if (((chunk_vt*)p_chunk)->mrkcnt == 0) { // fast threading
    for (i = 0 ; i < itmtot ; i += 1) {
      *p_data = (freeitmlst_vt)xs ; xs = p_data ; p_data += itmwsz ;
    } // end of [for]
    the_freeitmlstarr[itmwsz_log] = xs ; return ;
  } // end of [if]
//
  mrkbits = ((chunk_vt*)p_chunk)->mrkbits ;
  for (i = 0 ; i < itmtot ; i += 1) {
    // add if not marked
    if (!MARKBIT_GET(mrkbits, i)) { *p_data = xs ; xs = (freeitmlst_vt)p_data ; }
    p_data += itmwsz ;
  } // end of [for]
//
  the_freeitmlstarr[itmwsz_log] = xs ; return ;
} // end of [gcats2_the_freeitmlstarr_add_chunk]

%} // end of [%{^]

(* ****** ****** *)

%{^

// implemented in [gcats2_top.dats]
extern freepagelst_vt the_chunkpagelst ;

extern // implemented in [gcats2_freeitmlst.dats]
ats_int_type gcats2_freeitmlst_length (ats_ptr_type) ;

ats_int_type
gcats2_the_chunkpagelst_length () {
  return gcats2_freeitmlst_length (the_chunkpagelst) ;
}

/*
fun the_chunkpagelst_insert {l:addr} // inserting one page
  (pf: !the_chunkpagelst_v, pf_page: freepage @ l | p: ptr l):<> void
// end of [...]
*/

ats_void_type
gcats2_the_chunkpagelst_insert
  (ats_ptr_type p_freepage) {
  *(freepagelst_vt*)p_freepage = the_chunkpagelst ;
  the_chunkpagelst = (freepagelst_vt)p_freepage ; return ;
} /* end of [gcats2_the_chunkpagelst_insert] */

/*
fun the_chunkpagelst_remove_opt // taking out one page
  (pf: !the_chunkpagelst_v | (*none*)):<> [l:addr] (ptropt_v (freepage, l) | ptr l)
// end of [...]
*/

ats_ptr_type
gcats2_the_chunkpagelst_remove_opt () {
  freepagelst_vt p_freepage = the_chunkpagelst ;
  if (p_freepage) the_chunkpagelst = *(freepagelst_vt*)p_freepage ;
  return p_freepage ;
} /* end of [gcats2_the_chunkpagelst_remove_opt] */

/*
fun the_chunkpagelst_replenish
  (pf: !the_chunkpagelst_v | (*none*)):<> void // adding N pages for some N >= 1
// end of [...]
*/
ats_int_type
gcats2_the_chunkpagelst_replenish
  (ats_int_type n0) {
  int n ; char *p0 ;
  p0 = (char*)gcats2_mmap_ext(n0 * CHUNK_BYTESIZE) ;
/*
  fprintf(stderr, "gcats2_the_chunkpagelst_replenish: mmap: p0 = %p\n", p0) ;
*/  
  gcats2_the_chunkpagelst_insert(p0) ; n = n0 - 1; // n0 > 0
  while (n > 0) {
    p0 += CHUNK_BYTESIZE ; gcats2_the_chunkpagelst_insert(p0) ; n -= 1 ;
  } // end of [while]
  return n0 ;
} /* gcats2_the_chunkpagelst_replenish */

%} // end of [%{^]

(* ****** ****** *)

%{^

extern
ats_ptr_type gcats2_the_chunkpagelst_remove () ;

ats_ptr_type
gcats2_chunk_make_norm (
  ats_size_type itmwsz
, ats_int_type itmwsz_log
) {
  int itmtot, nbyte ;
  freepageptr_vt p_freepage ;
  chunkptr_vt p_chunk ;
#if (GCATS2_DEBUG > 0)
  if (itmwsz != (1 << itmwsz_log)) {
    fprintf(stderr, "gcats2_chunk_make_norm: itmwsz = %lu\n", itmwsz) ;
    fprintf(stderr, "gcats2_chunk_make_norm: itmwsz_log = %i\n", itmwsz_log) ;
    exit(1) ;
  } // end of [if]
#endif
  itmtot = (CHUNK_WORDSIZE >> itmwsz_log) ;
  p_chunk = (chunkptr_vt)gcats2_malloc_ext(sizeof(chunk_vt)) ;
  p_freepage = (freepageptr_vt)gcats2_the_chunkpagelst_remove() ;
//
  p_chunk->itmwsz = itmwsz ;
  p_chunk->itmwsz_log = itmwsz_log ;
  p_chunk->itmtot = itmtot ;
  nbyte = (itmtot + NBIT_PER_BYTE_MASK) >> NBIT_PER_BYTE_LOG ;
//
  p_chunk->mrkcnt = 0 ; // for fast threading!
  memset(p_chunk->mrkbits, 0, nbyte) ;
//
  p_chunk->chunk_data = p_freepage ;
  p_chunk->sweepnxt = (chunklst_vt)0 ;
/*
  fprintf(stderr, "chunk_make_norm: p_chunk(%p) =\n", p_chunk) ;
  gcats2_fprint_chunk(stderr, p_chunk) ;
*/
  return p_chunk ;
} /* end of [gcats2_chunk_make_norm] */

/*
fun chunk_free_norm {l:agz}
  (pf: !the_chunkpagelst_v | p_chunk: chunkptr_vt l):<> void
*/
ats_void_type
gcats2_chunk_free_norm
  (ats_ptr_type p_chunk) { // p_chunk != NULL
#if (GCATS2_DEBUG > 0)
  if (((chunk_vt*)p_chunk)->itmwsz_log < 0) {
    fprintf(stderr, "gcats2_chunk_free_norm: the chunk to be freed is large.\n") ;
    exit(1) ;
  } // end of [if]
#endif
  gcats2_the_chunkpagelst_insert(((chunk_vt*)p_chunk)->chunk_data) ;
/*  
  fprintf(stderr, "chunk_free_norm: p_chunk(%p) =\n", p_chunk) ;
  gcats2_fprint_chunk(stderr, p_chunk) ;
*/
  gcats2_free_ext(p_chunk) ;
  return ;
} /* end of [gcats2_chunk_free_norm] */

%} // end of [%{^]

(* ****** ****** *)

%{^

ats_ptr_type
gcats2_chunk_make_large (
  ats_size_type itmwsz // itmwsz > CHUNK_WORDSIZE
) {
  size_t nchunk ;
  chunkptr_vt p_chunk ; freepageptr_vt p_freepage ;
#if (GCATS2_DEBUG > 0)
  if (itmwsz <= CHUNK_WORDSIZE) {
    fprintf(stderr, "gcats2_chunk_make_large: itmwsz = %i\n", itmwsz) ;
    exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG > 0]
  nchunk = (itmwsz + CHUNK_WORDSIZE_MASK) >> CHUNK_WORDSIZE_LOG ;

  p_chunk = (chunkptr_vt)gcats2_malloc_ext(sizeof(chunk_vt)) ;
  p_freepage = (char*)gcats2_mmap_ext(nchunk * CHUNK_BYTESIZE) ;
//
  p_chunk->itmwsz = nchunk * CHUNK_WORDSIZE ;
  p_chunk->itmwsz_log = -1 ; // indicating being large
  p_chunk->itmtot = 1 ;
//
  p_chunk->mrkcnt = 0 ; // for fast threading!
  MARKBIT_CLEAR (p_chunk->mrkbits, 1) ; // only 1 bit is needed
//
  p_chunk->chunk_data = p_freepage ;
  p_chunk->sweepnxt = (chunklst_vt)0 ;
/*
  fprintf(stderr, "chunk_make_large: p_chunk(%p) =\n", p_chunk) ;
  gcats2_fprint_chunk(stderr, p_chunk) ;
*/
  return p_chunk ;
} /* end of [gcats2_chunk_make_large] */

ats_void_type
gcats2_chunk_free_large
  (ats_ptr_type p_chunk) { // p_chunk != NULL
#if (GCATS2_DEBUG > 0)
  if (((chunk_vt*)p_chunk)->itmwsz_log >= 0) {
    fprintf(stderr, "gcats2_chunk_free_large: the chunk to be freed is normal.\n") ;
    exit(1) ;
  } // end of [if]
#endif
  gcats2_munmap_ext(
    ((chunk_vt*)p_chunk)->chunk_data, (((chunk_vt*)p_chunk)->itmwsz) << NBYTE_PER_WORD_LOG
  ) ;
/*  
  fprintf(stderr, "chunk_free_large: p_chunk(%p) =\n", p_chunk) ;
  gcats2_fprint_chunk(stderr, p_chunk) ;
*/
  gcats2_free_ext(p_chunk) ;
  return ;
} /* end of [gcats2_chunk_free_large] */

%} // end of [%{^]

(* ****** ****** *)

%{^

static  // the number of botsegtbls that
long int the_nbotsegtbl_alloc = 0 ; // is allocated

ats_lint_type
gcats2_the_nbotsegtbl_alloc_get () { return the_nbotsegtbl_alloc ; }
// end of ...

ats_int_type
gcats2_the_topsegtbl_insert_chunkptr
  (ats_ptr_type p_chunk) {
  freeitmptr_vt p_chunk_data ;
  topseg_t ofs_topseg ; int ofs_botseg ; // ofs_chkseg == 0
  botsegtblptr_vt p_botsegtbl, *r_p_botsegtbl ;
  chunkptr_vt *r_p_chunk ;

  p_chunk_data = ((chunk_vt*)p_chunk)->chunk_data ;
  ofs_topseg = PTR_TOPSEG_GET(p_chunk_data) ;
  r_p_botsegtbl =
    (botsegtblptr_vt*)(gcats2_the_topsegtbl_takeout(ofs_topseg)) ;
  p_botsegtbl = *r_p_botsegtbl ;
  if (!p_botsegtbl) {
    p_botsegtbl =
      gcats2_malloc_ext(sizeof(botsegtbl_vt)) ;
    the_nbotsegtbl_alloc += 1 ;
    memset(p_botsegtbl, 0, sizeof(botsegtbl_vt)) ;
#if (__WORDSIZE == 64)
     p_botsegtbl->hashkey = (uintptr_t)ofs_topseg ; p_botsegtbl->hashnext = (botsegtblptr_vt)0 ;
#endif // end of [__WORDSIZE == 64]
/*
    fprintf(stderr,
      "gcats2_the_topsegtbl_insert_chunkptr: the_nbotsegtbl_alloc = %i\n", the_nbotsegtbl_alloc
    ) ;
*/
    *r_p_botsegtbl = p_botsegtbl ;
  } // end of [if]
  ofs_botseg = PTR_BOTSEG_GET(p_chunk_data) ;
  r_p_chunk = gcats2_botsegtblptr1_takeout(p_botsegtbl, ofs_topseg, ofs_botseg) ;
//
#if (__WORDSIZE == 64)
  if (!r_p_chunk) {
    p_botsegtbl =
      gcats2_malloc_ext(sizeof(botsegtbl_vt)) ;
    the_nbotsegtbl_alloc += 1 ;
    memset(p_botsegtbl, 0, sizeof(botsegtbl_vt)) ;
    p_botsegtbl->hashkey = (uintptr_t)ofs_topseg ; p_botsegtbl->hashnext = *r_p_botsegtbl ;
/*
    fprintf(stderr,
      "gcats2_the_topsegtbl_insert_chunkptr: the_nbotsegtbl_alloc = %i\n", the_nbotsegtbl_alloc
    ) ;
*/
    *r_p_botsegtbl = p_botsegtbl ;
    (p_botsegtbl->headers)[ofs_botseg] = p_chunk ;
    return 0 ;
  } // end of [if]
#endif // end of [__WORDSIZE == 64]
//
#if (GCATS2_DEBUG > 0)
  if (*r_p_chunk != (chunkptr_vt)0) {
/*
    fprintf(stderr,
      "exit(ATS/GC): gcats2_the_topsegtbl_insert_chunkptr: p_chunk = %p\n", p_chunk
    ) ;
    fprintf(stderr,
      "exit(ATS/GC): gcats2_the_topsegtbl_insert_chunkptr: *r_p_chunk = %p\n", *r_p_chunk
    ) ;
    exit(1) ;
*/
    return 1 ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG > 0]
//
  *r_p_chunk = p_chunk ; return 0 ;
} /* end of [gcats2_the_topsegtbl_insert_chunkptr] */

/* ****** ****** */

ats_ptr_type // chunkptr
gcats2_the_topsegtbl_remove_chunkptr
  (ats_ptr_type ptr) {
  // ptr = p_chunk->chunk_data if p_chunk is removed
  topseg_t ofs_topseg ; int ofs_botseg ; // ofs_chkseg == 0
  botsegtblptr_vt p_botsegtbl;
  chunkptr_vt p_chunk, *r_p_chunk ;

  ofs_topseg = PTR_TOPSEG_GET(ptr) ;
  p_botsegtbl = // pf_botsegtbl, fpf_topsegtbl
    *(botsegtblptr_vt*)(gcats2_the_topsegtbl_takeout(ofs_topseg)) ;
  if (!p_botsegtbl) return (chunkptr_vt)0 ; // error return
  ofs_botseg = PTR_BOTSEG_GET(ptr) ;
  r_p_chunk = gcats2_botsegtblptr1_takeout(p_botsegtbl, ofs_topseg, ofs_botseg) ;
  if (!r_p_chunk) { return (chunkptr_vt)0 ; } // error return
  p_chunk = *r_p_chunk ; *r_p_chunk = (chunkptr_vt)0 ;
#if (GCATS2_DEBUG > 0)
  if (ptr != p_chunk->chunk_data) {
    fprintf(stderr, "exit(ATS/GC): gcats2_the_topsegtbl_remove_chunkptr: ptr = %p\n", ptr) ;
    fprintf(stderr, "exit(ATS/GC): gcats2_the_topsegtbl_remove_chunkptr: p_chunk = %p\n", p_chunk) ;
    exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG > 0]
  return p_chunk ;
} /* end of ... */

%} // end of [ %{^ ]

(* ****** ****** *)

%{^

ats_void_type
gcats2_the_topsegtbl_foreach_chunkptr
  (ats_ptr_type f, ats_ptr_type env) {
  int i, j ;
  botsegtblptr_vt p_botsegtbl ;
  chunkptr_vt p_chunk ;
//
#if (__WORDSIZE == 32)
  for (i = 0; i < TOPSEG_TABLESIZE; i += 1) {
    p_botsegtbl = the_topsegtbl[i] ;
    if (p_botsegtbl) {
      for (j = 0; j < BOTSEG_TABLESIZE; j += 1) {
        p_chunk = p_botsegtbl->headers[j] ;
        if (p_chunk) ((ats_void_type (*)(ats_ptr_type, ats_ptr_type))f)(p_chunk, env) ;
      } // end of [for]
    } // end of [if]
  } // end of [for]
#endif // end of ...
//
#if (__WORDSIZE == 64)
  for (i = 0; i < TOPSEG_HASHTABLESIZE; i += 1) {
    p_botsegtbl = the_topsegtbl[i] ;
    while (p_botsegtbl) {
      for (j = 0; j < BOTSEG_TABLESIZE; j += 1) {
        p_chunk = p_botsegtbl->headers[j] ;
        if (p_chunk) ((ats_void_type (*)(ats_ptr_type, ats_ptr_type))f)(p_chunk, env) ;
      } // end of [for]
      p_botsegtbl = p_botsegtbl->hashnext ;
    } // end of [while]
  } // end of [for]
#endif // end of ...
//
  return ;
} /* end of [gcats2_the_topsegtbl_foreach_chunkptr] */

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_chunk.dats] *)
