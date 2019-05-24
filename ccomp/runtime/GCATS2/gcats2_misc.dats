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

// #include "gcats2_ats.hats"

(* ****** ****** *)

#define ATSOPT_NAMESPACE "gcats2_misc_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

%{^

static int the_mystackdir = 0 ;

// dir=1/-1 : upward/downward
static
ats_int_type // volatile // no inline!
gcats2_mystackdir_get_main (
  void *some_arg // a stack pointer obtained previously
) {
  void *some_ptr ;
  if ((void*)&some_ptr > some_arg) return 1 ; else return -1 ;
  return 0 ; /* deadcode */
} /* end of [gcats2_mystackdir_get_main] */

ats_int_type
gcats2_mystackdir_get () {
  void *some_ptr ;
  if (!the_mystackdir) { // uninitialized
    the_mystackdir = gcats2_mystackdir_get_main (&some_ptr) ;
  }
  return the_mystackdir ;
} /* end of [gcats2_mystackdir_get] */

/* ****** ****** */

static
#if (_ATS_MULTITHREAD)
__thread // thread-local storage
#endif // end of ...
ats_ptr_type the_mystackbeg = (ats_ptr_type)0 ;

ats_void_type
gcats2_mystackbeg_set (
  ats_int_type dir // dir = gcats2_mystackdir_get
) {
  long int pagesize, pagemask ; uintptr_t beg ;

  if (the_mystackbeg) return ; // [the_mystackbeg] is already set

  // pagesize must be a power of 2
  pagesize = sysconf(_SC_PAGESIZE) ; // system configuration // usually 4096
  pagemask = ~(pagesize - 1) ; // 1...10...0

  if (dir > 0) {
    beg = (uintptr_t)(&pagesize) ;
    beg &= pagemask ;
  } else {
    beg = (uintptr_t)(&pagesize) + pagesize ;
    beg &= pagemask ;
    beg -= sizeof(freeitmptr_vt) ;
  }
  the_mystackbeg = (ats_ptr_type)beg ;
// /*
  fprintf(stderr, "gcats2_mystackbeg_set: dir = %i\n", dir) ;
  fprintf(stderr, "gcats2_mystackbeg_set: pagesize = %li\n", pagesize) ;
  fprintf(stderr, "gcats2_mystackbeg_set: &pagesize = %p\n", &pagesize) ;
  fprintf(stderr, "gcats2_mystackbeg_set: beg = %p\n", (void*)beg) ;
// */
  return ;
} /* end of [gcats2_mystackbeg_set] */

ats_ptr_type
gcats2_mystackbeg_get (
  // there is no argument for this function
) {
  if (!the_mystackbeg) { fprintf (stderr,
      "INTERNAL ERROR(ATS/GC): [gcats2_mystackbeg_get]: the_mystackbeg is not yet set.\n"
    ) ; exit (1) ;
  } // end of [if]
  return the_mystackbeg ;
} /* end of [gcats2_mystackbeg_get] */

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_misc.dats] *)
