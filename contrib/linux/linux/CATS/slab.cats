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
** ATS is  free software;  you can redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
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
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Start Time: February, 2011
//
/* ****** ****** */

#ifndef ATSCTRB_LINUX_LINUX_SLAB_CATS
#define ATSCTRB_LINUX_LINUX_SLAB_CATS

/* ****** ****** */

#include <linux/slab.h>

/* ****** ****** */

#define atsctrb_linux_kmalloc kmalloc
#define atsctrb_linux_kfree kfree

/* ****** ****** */

#define atsctrb_linux_slab_is_available slab_is_available
#define atsctrb_linux_kmem_cache_size kmem_cache_size
#define atsctrb_linux_kmem_cache_name kmem_cache_name

#define atsctrb_linux_kmem_cache_create kmem_cache_create
#define atsctrb_linux_kmem_cache_destroy kmem_cache_destroy

#define atsctrb_linux_kmem_cache_alloc kmem_cache_alloc
#define atsctrb_linux_kmem_cache_free kmem_cache_free

/* ****** ****** */

#endif /* ATSCTRB_LINUX_LINUX_SLAB_CATS */

/* end of [slab.cats] */
