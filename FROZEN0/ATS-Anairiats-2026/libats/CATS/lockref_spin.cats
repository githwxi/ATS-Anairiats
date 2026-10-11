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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*/

/* ****** ****** */

/*
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) 
**
*/

/* ****** ****** */

#ifndef ATS_LIBATS_LOCKREF_SPIN_CATS
#define ATS_LIBATS_LOCKREF_SPIN_CATS

/* ****** ****** */

#include "libats/CATS/lockptr_spin.cats"

/* ****** ****** */

#define atslib_lockref_create_locked atslib_lockptr_create_locked
#define atslib_lockref_create_unlocked atslib_lockptr_create_unlocked

/* ****** ****** */

#define atslib_lockref_acquire atslib_lockptr_acquire
#define atslib_lockref_acquire_try atslib_lockptr_acquire_try
#define atslib_lockref_release atslib_lockptr_release

/* ****** ****** */

#endif // end of [#ifndef ATS_CONTRIB_LOCKREF_SPIN_CATS]

/* ****** ****** */

/* end of [lockref_spin.cats] */
