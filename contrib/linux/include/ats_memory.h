/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*/

/* ****** ****** */
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) 
// Start Time: February, 2011
//
/* ****** ****** */

#ifndef	ATS_MEMORY_H
#define ATS_MEMORY_H

/* ****** ****** */

#define ATS_FREE(ptr) kfree(ptr)
#define ATS_MALLOC(bsz) kmalloc(bsz, GFP_KERNEL)

/* ****** ****** */

#endif	/* ATS_MEMORY_H */

/* end of [ats_memory.h] */
