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

#define ATSOPT_NAMESPACE "gcats2_globalrts_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

%{^

typedef
struct globalrtspage_struct {
  struct globalrtspage_struct *next ;
/*
**struct globalrtspage_struct *prev ; // no need to go backward
*/
  ptrsize_t entries[GLOBALRTS_PAGESIZE] ;
} globalrtspage_vt ;

typedef globalrtspage_vt *globalrtspagelst_vt ;

/* ****** ****** */

globalrtspage_vt the_globalrtspage_fst = {0} ;

globalrtspagelst_vt // it should never be NULL!
the_globalrtspagelst_cur = &the_globalrtspage_fst ;

int the_globalrtsposition = 0 ; // the_globalrtsposition : natLt (GLOBALRTS_PAGESIZE)

/* ****** ****** */

/*
fun the_globalrts_insert
  (pf: !the_globalrts_v | ptr: ptr, wsz: size_t):<> void
  = "gcats2_the_globalrts_insert"
*/

ats_void_type
gcats2_the_globalrts_insert (
  ats_ptr_type ptr, ats_size_type wsz
) {
  ptrsize_t *p_entry ;
/*
  fprintf(stderr, "gcats2_the_globalrts_insert: ptr = %p\n", ptr) ;
  fprintf(stderr, "gcats2_the_globalrts_insert: wsz = %lu\n", wsz) ;
*/
  p_entry = &(the_globalrtspagelst_cur->entries[the_globalrtsposition]) ;
  the_globalrtsposition += 1 ;
  p_entry->ptr = ptr ; p_entry->wsz = wsz ;
  if (the_globalrtsposition == GLOBALRTS_PAGESIZE) {
    the_globalrtsposition = 0 ;
    the_globalrtspagelst_cur->next = gcats2_malloc_ext(sizeof(globalrtspage_vt)) ;
    the_globalrtspagelst_cur = the_globalrtspagelst_cur->next ;
  } // end of [if]
  return ;
} // end of [gcats2_the_globalrts_insert]

/* ****** ****** */

extern ats_int_type
gcats2_ptrsize_mark (ats_ptr_type ptr, ats_size_type wsz) ;

ats_int_type
gcats2_the_globalrts_mark (
  // there is no argument for this function
) {
  int i ;
  globalrtspage_vt *p_page ; ptrsize_t *p_entry ;
  int overflow = 0 ;
/*
  fprintf(stderr, "gcats2_the_globalrts_mark: starts\n") ;
*/
  p_page = &the_globalrtspage_fst ;
  while (p_page != the_globalrtspagelst_cur) {
    p_entry = &(p_page->entries[0]) ;
    for (i = 0; i < GLOBALRTS_PAGESIZE; i += 1) {
      overflow += gcats2_ptrsize_mark(p_entry->ptr, p_entry->wsz) ;
      p_entry += 1 ;
    } // end of [for]
    p_page = p_page->next ;
  } // end of [while]
// last page is not full in general
  p_entry = &(p_page->entries[0]) ;
  for (i = 0; i < the_globalrtsposition; i += 1) {
/*
    fprintf(stderr, "gcats2_the_globalrts_mark: ptr = %p\n", p_entry->ptr) ;
    fprintf(stderr, "gcats2_the_globalrts_mark: wsz = %lu\n", p_entry->wsz) ;
*/
    overflow += gcats2_ptrsize_mark(p_entry->ptr, p_entry->wsz) ; p_entry += 1 ;
  } // end of [for]
/*
  fprintf(stderr, "gcats2_the_globalrts_mark: finishes: overflow = %i\n", overflow) ;
*/
  return overflow ;
} // gcats2_the_globalrts_mark

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_globalrts.dats] *)
