/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
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
*/

/* ****** ****** */

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2009

/* ****** ****** */

/* include some .h files */
#include "ats_config.h"
#include "ats_basics.h"
#include "ats_types.h"
#include "ats_exception.h"
#include "ats_memory.h"

/* ****** ****** */

/* include some .cats files */
#include "prelude/CATS/array.cats"
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/string.cats"

/* ****** ****** */

#include "gcats2.cats"

#include "gcats2_top_dats.c"
#include "gcats2_misc_dats.c"
#include "gcats2_freeitmlst_dats.c"
#include "gcats2_chunk_dats.c"
#include "gcats2_pointer_dats.c"
#include "gcats2_globalrts_dats.c"

#include "gcats2_marking_dats.c"
#include "gcats2_collecting_dats.c"
#include "gcats2_autmem_dats.c"
#include "gcats2_manmem_dats.c"

#if (_ATS_MULTITHREAD)
#include "gcats2_multithread_dats.c"
#endif // end of [_ATS_MULTITHREAD]

#include "gcats2_sats.c"

/* ****** ****** */

/* end of [gcats2_all.cats] */
