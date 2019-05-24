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

#ifndef ATSCTRB_GRAPHVIZ_GVC_CATS
#define ATSCTRB_GRAPHVIZ_GVC_CATS

/* ****** ****** */

#include "graphviz/gvc.h"

/* ****** ****** */

#include "contrib/graphviz/CATS/types.cats"

/* ****** ****** */

#define atsctrb_gvContext gvContext

ATSinline()
ats_ptr_type
atsctrb_gvContext_exn
  () {
  ats_ptr_type gvc = gvContext() ;
  if (!gvc) {
    fprintf (stderr, "[gvContext()] failded.\n") ;
    exit (1) ;
  } // end of [if]
  return gvc ;
} // end of [atsctrb_gvContext_exn]

/* ****** ****** */

#define atsctrb_gvcVersion gvcVersion
#define atsctrb_gvcBuildDate gvcBuildDate

/* ****** ****** */

ATSinline()
ats_int_type
atsctrb_gvFreeContext0
  (ats_ptr_type gvc) {
  if (!gvc) return 0 ; else return gvFreeContext(gvc) ;
} // end of [atsctrb_gvFreeContext0]

#define atsctrb_gvFreeContext1 gvFreeContext

/* ****** ****** */

#define atsctrb_gvLayout gvLayout
#define atsctrb_gvRender gvRender
#define atsctrb_gvRenderFilename gvRenderFilename

#define atsctrb_gvFreeLayout gvFreeLayout

/* ****** ****** */

#endif // end of [ATSCTRB_GRAPHVIZ_GVC_CATS]

/* end of [gvc.cats] */
