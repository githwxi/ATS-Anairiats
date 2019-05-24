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

#include "gcats2_ats.hats"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"
staload UNISTD = "libc/SATS/unistd.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

fn ptr_randgen (): ptr = let
  fun loop {n:nat} .<n>.
    (n: int n, u: ulint):<!ref> ulint =
    if n > 0 then let
      val b = ulint_of_int ($RAND.randint 2)
    in
      loop (n-1, (u << 1) lor b)
    end else
      u // loop exits
    // end of [if]
  val u = loop (__WORDSIZE, 0UL)
in
  ptr_of_uintptr (uintptr_of_ulint u)
end // end of [ptr_randgen]

(*
// for testing the "randomness" of [ptr_randgen]
val () = loop () where {
  fun loop () = begin
    $UNISTD.usleep (12345);
    $RAND.srand48_with_gettimeofday ();
    print "ptr = "; print (ptr_randgen ()); print_newline ();
    loop ()
  end // end of [loop]
} // end of [val]
*)

(* ****** ****** *)

fn ptr_topbotchk_test () = let
  #define N 1000
  val () = (
    printf ("[ptr_topbotchk_test]: start: N = %i\n", @(N))
  ) // end of [val]
  fn do_one (): void = let
    val ptr = ptr_randgen ()
    val u_ptr = uintptr_of_ptr (ptr)
//
    val u_top = uintptr_of_topseg (PTR_TOPSEG_GET ptr)
    val u_bot = uintptr_of_uint (uint_of_int (PTR_BOTSEG_GET ptr))
    val u_chk = uintptr_of_uint (uint_of_int (PTR_CHKSEG_GET ptr))
    val u = u_top
    val u = (u << PTR_BOTSEG_SIZE) lor u_bot
    val u = (u << PTR_CHKSEG_SIZE) lor u_chk
    val u = u << NBYTE_PER_WORD_LOG
    val u = u lxor u_ptr
(*
    val () = printf ("ptr = %p\n", @(ptr))
    val () = printf ("top = %p\n", @(ptr_of_uintptr u_top))
    val () = printf ("bot = %p\n", @(ptr_of_uintptr u_bot))
    val () = printf ("chk = %p\n", @(ptr_of_uintptr u_chk))
*)
    // val () = printf ("u = %u\n", @(uint_of_uintptr u))
    val () = assert_errmsg (uint_of_uintptr u < uint_of_int NBYTE_PER_WORD, #LOCATION)
  in
    // nothing
  end // end of [loop]
  var i: int // unintialized
  val () = for (i := 0; i < N; i := i + 1) do_one ()
in
  // nothing
end // end of [ptr_topbotchk_test]

(* ****** ****** *)

fn nchunktot_get
  (pf_tbl: !the_topsegtbl_v | (*none*)): int = n where {
  var n: int = 0
  viewdef v = int @ n; viewtypedef vt = ptr n
  fn f {l:anz}
    (pf_tbl: !the_topsegtbl_v, pf: !v | p_chunk: !chunkptr_vt l, p_n: !vt):<> void = let
    val p = ptr_of_chunkptr (p_chunk)
  in
    !p_n := !p_n + 1
  end // end of [f]
  val () = the_topsegtbl_foreach_chunkptr {v} {vt} (pf_tbl, view@ n | f, &n)
} // end of [nchunktot_get]

(* ****** ****** *)

fn the_topsegtbl_insert_remove_test (
    pf1: !the_totwsz_v
  , pf2: !the_topsegtbl_v
  , pf3: !the_chunkpagelst_v
  | (*none*)
  ) : void = () where {
  #define N 10
  #define ITMWSZ 32
  #define ITMWSZ_LOG 5
  #define ITMTOT %(CHUNK_WORDSIZE / ITMWSZ)
  val () = (
    printf ("[the_topsegtbl_insert_remove_test]: start: N = %i\n", @(N))
  ) // end of [val]
  viewtypedef ptrlst = List_vt ptr
  val ptrs = loop
    (pf1, pf2, pf3 | N, list_vt_nil ()) where {
    fun loop {n:nat} (
        pf1: !the_totwsz_v
      , pf2: !the_topsegtbl_v
      , pf3: !the_chunkpagelst_v
      | n: int n, ptrs: ptrlst
      ) : ptrlst =
      if n > 0 then let
        val p_chunk = chunk_make_norm (pf1, pf3 | ITMWSZ, ITMWSZ_LOG)
        val (pf_chunk | p) = chunkptr_unfold (p_chunk)
        val p_chunk_data = chunk_data_get (!p)
        val _(*ptr*) = chunkptr_fold (pf_chunk | p_chunk)
        val err = the_topsegtbl_insert_chunkptr (pf2 | p_chunk)
        val () = assert_errmsg (err = 0, #LOCATION)
      in
        loop (pf1, pf2, pf3 | n-1, list_vt_cons (p_chunk_data, ptrs))
      end else
        ptrs // loop exits
      // end of [if]
    // end of [loop]
  } // end of [val ptrs]
  val () = the_topsegtbl_clear_mrkbits (pf2 | (*none*))
  val nchunk = nchunktot_get (pf2 | (*none*))
  val () = (print "nchunk = "; print nchunk; print_newline ())
  val () = loop (pf1, pf2, pf3 | ptrs) where {
    fun loop (
        pf1: !the_totwsz_v
      , pf2: !the_topsegtbl_v
      , pf3: !the_chunkpagelst_v
      | ptrs: ptrlst
      ) : void =
      case+ ptrs of
      | ~list_vt_cons (ptr, ptrs) => let
          val p_chunk = the_topsegtbl_remove_chunkptr (pf2 | ptr)
          val () = assert_errmsg (ptr_of_chunkptr p_chunk <> null, #LOCATION)
          val () = chunk_free_norm (pf1, pf3 | p_chunk)
        in
          loop (pf1, pf2, pf3 | ptrs)
        end // end of [list_vt_cons]
      | ~list_vt_nil () => ()
    // end of [loop]
  } // end of [val ()]
  val nchunk = nchunktot_get (pf2 | (*none*))
  val () = (print "nchunk = "; print nchunk; print_newline ())
} // end of [the_topsegtbl_insert_remove_test]

(* ****** ****** *)

fn ptr_isvalid_test (
    pf1: !the_totwsz_v
  , pf2: !the_topsegtbl_v
  , pf3: !the_chunkpagelst_v
  | (*none*)
  ) : void = () where {
  #define ITMWSZ 4
  #define ITMWSZ_LOG 2
  #define ITMBSZ %(ITMWSZ * NBYTE_PER_WORD)
  val () = (
    printf ("[ptr_isvalid_test]: start\n", @())
  ) // end of [val]
  val nchunkpage_bef = the_chunkpagelst_length (pf3 | (*none*))
  val () = (print "nchunkpage(bef) = "; print nchunkpage_bef; print_newline ())
  val p0_chunk = chunk_make_norm (pf1, pf3 | ITMWSZ, ITMWSZ_LOG)
  val nchunkpage_aft = the_chunkpagelst_length (pf3 | (*none*))
  val () = (print "nchunkpage(aft) = "; print nchunkpage_aft; print_newline ())
  val () = assert_errmsg (nchunkpage_bef = nchunkpage_aft + 1, #LOCATION)
  val (pf0_chunk | p0) = chunkptr_unfold (p0_chunk)
  val ptr0 = chunk_data_get (!p0)
  val _(*p0*) = chunkptr_fold (pf0_chunk | p0_chunk)
  val err = the_topsegtbl_insert_chunkptr (pf2 | p0_chunk)
  var nitm : int // uninitialized
//
  // this one is valid
  val (fpf2 | p0_chunk) = ptr_isvalid (pf2 | ptr0, nitm)
  val p0_chunk_1 =  ptr_of_chunkptr (p0_chunk)
  prval () = pf2 := fpf2 (p0_chunk)
  val () = assert_errmsg (p0_chunk_1 <> null, #LOCATION)
  prval () = opt_unsome (nitm)
//
  // this one is not valid
  val ptr1 = ptr_of_uintptr (uintptr_of_ptr ptr0 + uint_of_int (ITMBSZ / 2))
  val (fpf2 | p0_chunk) = ptr_isvalid (pf2 | ptr1, nitm)
  val p0_chunk_1 =  ptr_of_chunkptr (p0_chunk)
  prval () = pf2 := fpf2 (p0_chunk)
  val () = assert_errmsg (p0_chunk_1 = null, #LOCATION)
  prval () = opt_unnone (nitm)
//
  // this one is valid
  val ptr2 = ptr_of_uintptr (uintptr_of_ptr ptr0 + uint_of_int (ITMBSZ * 7))
  val (fpf2 | p0_chunk) = ptr_isvalid (pf2 | ptr2, nitm)
  val p0_chunk_1 =  ptr_of_chunkptr (p0_chunk)
  prval () = pf2 := fpf2 (p0_chunk)
  val () = assert_errmsg (p0_chunk_1 <> null, #LOCATION)
  prval () = opt_unsome (nitm)
//
  // this one is not valid
  val ptr2 = ptr_randgen ()
  val (fpf2 | p0_chunk) = ptr_isvalid (pf2 | ptr2, nitm)
  val p0_chunk_1 =  ptr_of_chunkptr (p0_chunk)
  prval () = pf2 := fpf2 (p0_chunk)
  val () = assert_errmsg (p0_chunk_1 = null, #LOCATION)
  prval () = opt_unnone (nitm)
} // end of [ptr_isvalid_test]

(* ****** ****** *)

fn the_manmemlst_test
  (pf: !the_manmemlst_v | (*none*)): void = let
  #define N 100
  val () = (
    printf ("[the_manmemlst_test]: start: N = %i\n", @(N))
  ) // end of [val]
  val ptrs = loop (pf | N, list_vt_nil) where {
    fun loop {i:nat} .<i>. (
        pf: !the_manmemlst_v | i: int i, res: List_vt ptr
      ) : List_vt ptr =
      if i > 0 then let
        val bsz = size1_of_int1 (i)
        val (pf_mm | p_mm) = manmem_create (bsz)
        val ptr = manmem_data_get (!p_mm)
        val () = the_manmemlst_insert (pf, pf_mm | p_mm)
      in
        loop (pf | i-1, list_vt_cons (ptr, res))
      end else
        res // loop exits
      // end of [if]
    // end of [loop]
  } // end of [val]
  val nmanmemlst = the_manmemlst_length (pf | (*none*))
  val () = begin
    print "the_manmemlst_test: nmanmemlst = "; print nmanmemlst; print_newline ()
  end
  val () = assert_errmsg (nmanmemlst = N, #LOCATION)
  val ptrs = list_vt_reverse (ptrs)
  val () = loop (pf | ptrs) where {
    fun loop (
        pf: !the_manmemlst_v | ptrs: List_vt ptr
      ) : void =
      case+ ptrs of
      | ~list_vt_cons (ptr, ptrs) => let
           val (pf_mm | p_mm) = the_manmemlst_remove (pf | ptr)
           val () = manmem_destroy (pf_mm | p_mm)
         in
           loop (pf | ptrs)
         end // end of [list_vt_cons]
      | ~list_vt_nil () => ()
    // end of [loop]
  } // end of [val]
  val nmanmemlst = the_manmemlst_length (pf | (*none*))
  val () = begin
    print "the_manmemlst_test: nmanmemlst = "; print nmanmemlst; print_newline ()
  end
  val () = assert_errmsg (nmanmemlst = 0, #LOCATION)
in
  // nothing
end // end of [the_manmemlst_test]

(* ****** ****** *)

dynload "gcats2_top.dats"

(*
dynload "gcats2_misc.dats"
dynload "gcats2_freeitmlst.dats"
dynload "gcats2_chunk.dats"
dynload "gcats2_pointer.dats"
dynload "gcats2_globalrts.dats"
dynload "gcats2_marking.dats"
dynload "gcats2_collecting.dats"
dynload "gcats2_autmem.dats"
dynload "gcats2_manmem.dats"
dynload "gcats2_multithread.dats"
*)

(* ****** ****** *)

#if (0) #then

implement main (argc, argv) = () where {
//
  val pagesz = $UNISTD.getpagesize ()
  val () = printf ("pagesize = %i\n", @(pagesz))
//
  val () = $RAND.srand48_with_gettimeofday ()
//
  prval (
    pf_the_totwsz, fpf_the_totwsz
  ) = pf_the_totwsz_gen () where { extern prfun
    pf_the_totwsz_gen (): (the_totwsz_v, the_totwsz_v -<prf> void)
  } // end of [prval]
//
  prval (
    pf_the_topsegtbl, fpf_the_topsegtbl
  ) = pf_the_topsegtbl_gen () where { extern prfun
    pf_the_topsegtbl_gen (): (the_topsegtbl_v, the_topsegtbl_v -<prf> void)
  } // end of [prval]
//
  prval (
    pf_the_chunkpagelst, fpf_the_chunkpagelst
  ) = pf_the_chunkpagelst_gen () where { extern prfun
    pf_the_chunkpagelst_gen (): (the_chunkpagelst_v, the_chunkpagelst_v -<prf> void)
  } // end of [prval]
//
  prval (
    pf_the_globalrts, fpf_the_globalrts
  ) = pf_the_globalrts_gen () where { extern prfun
    pf_the_globalrts_gen (): (the_globalrts_v, the_globalrts_v -<prf> void)
  } // end of [prval]
//
  prval (
    pf_the_manmemlst, fpf_the_manmemlst
  ) = pf_the_manmemlst_gen () where { extern prfun
    pf_the_manmemlst_gen (): (the_manmemlst_v, the_manmemlst_v -<prf> void)
  } // end of [prval]
//
  prval (
    pf_the_markstack, fpf_the_markstack
  ) = pf_the_markstack_gen () where { extern prfun
    pf_the_markstack_gen (): (the_markstack_v, the_markstack_v -<prf> void)
  } // end of [prval]
//
  val () = ptr_topbotchk_test ()
  val () = (print "[ptr_topbotchk_test] is done successfully."; print_newline ())
//
  val () = the_topsegtbl_insert_remove_test
    (pf_the_totwsz, pf_the_topsegtbl, pf_the_chunkpagelst | (*none*))
  val () = (print "[the_topsegtbl_insert_remove_test] is done successfully."; print_newline ())
//
  val () = ptr_isvalid_test
    (pf_the_totwsz, pf_the_topsegtbl, pf_the_chunkpagelst | (*none*))
  val () = (print "[ptr_isvalid_test] is done successfully."; print_newline ())
//
  val () = the_manmemlst_test (pf_the_manmemlst | (*none*))
  val () = (print "[the_manmemlst_test] is done successfully."; print_newline ())
//
  val nmarkstackpage =
    the_markstackpagelst_length (pf_the_markstack | (*none*))
  val () = (print "nmarkstackpage(bef) = "; print nmarkstackpage; print_newline ())
  val () = the_markstackpagelst_extend (pf_the_markstack | 5)
  val nmarkstackpage =
    the_markstackpagelst_length (pf_the_markstack | (*none*))
  val () = (print "nmarkstackpage(aft1) = "; print nmarkstackpage; print_newline ())
  val () = the_markstackpagelst_extend (pf_the_markstack | 7)
  val nmarkstackpage =
    the_markstackpagelst_length (pf_the_markstack | (*none*))
  val () = (print "nmarkstackpage(aft2) = "; print nmarkstackpage; print_newline ())
//
  prval () = fpf_the_totwsz (pf_the_totwsz)
  prval () = fpf_the_topsegtbl (pf_the_topsegtbl)
  prval () = fpf_the_chunkpagelst (pf_the_chunkpagelst)
  prval () = fpf_the_globalrts (pf_the_globalrts)
  prval () = fpf_the_manmemlst (pf_the_manmemlst)
  prval () = fpf_the_markstack (pf_the_markstack)
//
  prval (
    pf_the_gcmain, fpf_the_gcmain
  ) = pf_the_gcmain_gen () where { extern prfun
    pf_the_gcmain_gen (): (the_gcmain_v, the_gcmain_v -<prf> void)
  } // end of [prval]
//
  val _(*overflow*) =
    the_globalrts_mark (pf_the_gcmain | (*none*))
  val () = mystackbeg_set (dir) where { val dir = mystackdir_get () }
  val _(*overflow*) = mystack_mark ()
//
  val () = gcmain_run (pf_the_gcmain | (*none*))
//
  prval () = fpf_the_gcmain (pf_the_gcmain)
} // end of [main]

#endif // end of [#if (0)]

(* ****** ****** *)

staload _ = "prelude/DATS/reference.dats"

(* ****** ****** *)

extern fun the_globalrts_insert
  (p: ptr, sz: size_t): void = "gcats2_the_globalrts_insert"

val r_ptr = ref<ptr> (null)

val r_ptr0 = ref<ptr> (null)
and r_ptr1 = ref<ptr> (null)

val () = let
  val (_ | p) = ref_get_view_ptr (r_ptr0)
  val () = the_globalrts_insert (p, 1)
  val (_ | p) = ref_get_view_ptr (r_ptr1)
  val () = the_globalrts_insert (p, 1)
in
  // nothing
end // end of [val]

extern fun __ptr_cons
  (p: ptr, x1: ptr, x2: ptr): ptr = "__ptr_cons"
extern fun __ptr_car (p: ptr): ptr = "__ptr_car"
extern fun __ptr_cdr (p: ptr): ptr = "__ptr_cdr"

implement main () = () where {
  val () = initialize () where {
    extern fun initialize ():<> void = "gcats2_initialize"
  } // end of [val]
  var ptr1 = autmem_calloc_bsz (NBYTE_PER_WORD, 128)
  val () = printf ("ptr1 = %p\n", @(ptr1))
  var ptr2 = autmem_calloc_bsz (NBYTE_PER_WORD, 256)
  val () = printf ("ptr2 = %p\n", @(ptr2))
  var ptr3 = autmem_calloc_bsz (NBYTE_PER_WORD, 256)
  val () = printf ("ptr3 = %p\n", @(ptr3))
  var ptr4 = autmem_calloc_bsz (NBYTE_PER_WORD, 256)
  val () = printf ("ptr4 = %p\n", @(ptr4))
  var ptr5 = autmem_calloc_bsz (NBYTE_PER_WORD, 128)
  val () = printf ("ptr5 = %p\n", @(ptr5))
  var ptr6 = autmem_calloc_bsz (NBYTE_PER_WORD, 128)
  val () = printf ("ptr6 = %p\n", @(ptr6))
(*
  var ptr7 = autmem_calloc_bsz (NBYTE_PER_WORD, 128)
  val () = printf ("ptr7 = %p\n", @(ptr7))
  var ptr8 = autmem_calloc_bsz (NBYTE_PER_WORD, 128)
  val () = printf ("ptr8 = %p\n", @(ptr8))
*)
  #define N 100
  local
    fun loop {n:nat} (eo: int, n: int n, res: ptr): ptr =
      if n > 0 then begin
        if (n mod 2 = eo) then let
          val p = autmem_calloc_bsz (NBYTE_PER_WORD, 32)
        in
          loop (eo, n-1, __ptr_cons (p, null, res))
        end else loop (eo, n-1, res)
      end else
        res // loop exits
      // end of [loop]
  in
    val () = !r_ptr := loop (0, N, null)
    val () = !r_ptr1 := loop (1, N, null)
  end // end of [local]
//
  val () = fprint (stdout_ref, "the_topsegtbl =\n")
  val () = fprint_the_topsegtbl (stdout_ref)
//
  val (pf_the_gcmain | ()) = the_gcmain_lock_acquire ()
  val () = gcmain_run (pf_the_gcmain | (*none*))
  val () = the_gcmain_lock_release (pf_the_gcmain | (*none*))
//
  val () = fprint (stdout_ref, "the_topsegtbl =\n")
  val () = fprint_the_topsegtbl (stdout_ref)
//
  val () = printf ("ptr1 = %p\n", @(ptr1))
  val () = printf ("ptr2 = %p\n", @(ptr2))
  val () = printf ("ptr3 = %p\n", @(ptr3))
  val () = printf ("ptr6 = %p\n", @(ptr6))
//
} // end of [main]

(* ****** ****** *)

%{$

ats_ptr_type
__ptr_cons
  (ats_ptr_type p, ats_ptr_type x1, ats_ptr_type x2) {
  ((ats_ptr_type*)p)[0] = x1; ((ats_ptr_type*)p)[1] = x2; return p ;
} // end of ...

ats_ptr_type
__ptr_car
  (ats_ptr_type p) {
  return ((ats_ptr_type*)p)[0] ;
} // end of ...

ats_ptr_type
__ptr_cdr
  (ats_ptr_type p) {
  return ((ats_ptr_type*)p)[1] ;
} // end of ...

%}

(* ****** ****** *)

(* end of [gcats2_test.dats] *)
