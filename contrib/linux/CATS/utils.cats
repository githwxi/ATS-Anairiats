/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2011 Hongwei Xi.
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

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATSCTRB_LINUX_UTILS_CATS
#define ATSCTRB_LINUX_UTILS_CATS

/* ****** ****** */

#include <linux/gfp.h>
#include <linux/slab.h>

/* ****** ****** */

ATSinline()
ats_ptr_type
atsctrb_linux_array_ptr_kalloc_tsz (
  ats_size_type asz, gfp_t flags, ats_size_type tsz
) {
  return kmalloc(asz * tsz, flags) ;
} // end of [atsctrb_linux_array_ptr_kalloc_tsz]

/* ****** ****** */

#define atsctrb_linux_array_ptr_kfree kfree

/* ****** ****** */

#endif /* ATSCTRB_LINUX_UTILS_CATS */

/* end of [utils.cats] */
