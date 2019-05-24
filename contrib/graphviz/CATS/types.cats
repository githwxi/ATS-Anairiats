/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
*/

/* ****** ****** */
//
// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: October, 2011
//
/* ****** ****** */

#ifndef ATSCTRB_GRAPHVIZ_TYPES_CATS
#define ATSCTRB_GRAPHVIZ_TYPES_CATS

/* ****** ****** */

#define atsctrb_aginit aginit

#define atsctrb_agopen agopen

ATSinline()
ats_ptr_type
atsctrb_agopen_exn (
  ats_ptr_type path, ats_int_type type
) {
  ats_ptr_type g = (void*)agopen((char*)path, type) ;
  if (!g) {
    fprintf (stderr, "[agopen] failed.\n") ; exit (1) ;
  } // end of [if]
  return g ;
} // end of [atsctrb_agopen_exn]

#define atsctrb_agclose agclose

#define atsctrb_agread agread

ATSinline()
ats_ptr_type
atsctrb_agread_exn (
  ats_ptr_type path
) {
  ats_ptr_type g = (void*)agread((FILE*)path) ;
  if (!g) {
    fprintf (stderr, "[agread] failed.\n") ; exit (1) ;
  } // end of [if]
  return g ;
} // end of [atsctrb_agread_exn]

#define atsctrb_agwrite agwrite

/* ****** ****** */

#define atsctrb_agstrdup agstrdup
#define atsctrb_agstrdup_html agstrdup_html
#define atsctrb_agstrfree agstrfree

/* ****** ****** */

#endif // end of [ATSCTRB_GRAPHVIZ_GVC_CATS]

/* end of [gvc.cats] */
