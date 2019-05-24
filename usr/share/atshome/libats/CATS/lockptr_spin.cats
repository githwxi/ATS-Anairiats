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

#ifndef ATS_LIBATS_LOCKPTR_SPIN_CATS
#define ATS_LIBATS_LOCKPTR_SPIN_CATS

/* ****** ****** */

#include "libc/CATS/pthread.cats"

/* ****** ****** */

extern
ats_ptr_type
atslib_pthread_spin_create_locked (ats_int_type pshared) ;
extern
ats_ptr_type
atslib_pthread_spin_create_unlocked (ats_int_type pshared) ;

/* ****** ****** */

#define atslib_lockptr_create_locked \
  atslib_pthread_spin_create_locked
#define atslib_lockptr_create_unlocked \
  atslib_pthread_spin_create_unlocked

/* ****** ****** */

#define atslib_lockptr_acquire atslib_pthread_spin_lock
#define atslib_lockptr_acquire_try atslib_pthread_spin_trylock
#define atslib_lockptr_release atslib_pthread_spin_unlock

/* ****** ****** */

#endif // end of [#ifndef ATS_CONTRIB_LOCKPTR_SPIN_CATS]

/* ****** ****** */

/* end of [lockptr_spin.cats] */
