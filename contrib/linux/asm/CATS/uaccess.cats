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

#ifndef ATSCTRB_LINUX_ASM_UACCESS_CATS
#define ATSCTRB_LINUX_ASM_UACCESS_CATS

/* ****** ****** */

#include <asm/uaccess.h>

/* ****** ****** */

#define atsctrb_linux_clear_user clear_user
#define atsctrb_linux_copy_to_user copy_to_user
#define atsctrb_linux_copy_from_user copy_from_user
#define atsctrb_linux_strlen_user strlen_user

/* ****** ****** */

#endif /* ATSCTRB_LINUX_ASM_UACCESS_CATS */

/* end of [uaccess.cats] */
