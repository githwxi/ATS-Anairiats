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

#ifndef ATSCTRB_LINUX_LINUX_KERNEL_CATS
#define ATSCTRB_LINUX_LINUX_KERNEL_CATS

/* ****** ****** */

#include <linux/kernel.h>

/* ****** ****** */

#define atsctrb_linux_KERN_EMERG(x) (KERN_EMERG x)
#define atsctrb_linux_KERN_ALERT(x) (KERN_ALERT x)
#define atsctrb_linux_KERN_CRIT(x) (KERN_CRIT x)
#define atsctrb_linux_KERN_ERR(x) (KERN_ERR x)
#define atsctrb_linux_KERN_WARNING(x) (KERN_WARNING x)
#define atsctrb_linux_KERN_NOTICE(x) (KERN_NOTICE x)
#define atsctrb_linux_KERN_INFO(x) (KERN_INFO x)
#define atsctrb_linux_KERN_DEBUG(x) (KERN_DEBUG x)

/* ****** ****** */

#define atsctrb_linux_printk printk

/* ****** ****** */

#endif /* ATSCTRB_LINUX_LINUX_KERNEL_CATS */

/* end of [kernel.cats] */
