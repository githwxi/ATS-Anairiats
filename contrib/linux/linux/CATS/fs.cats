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

#ifndef ATSCTRB_LINUX_LINUX_FS_CATS
#define ATSCTRB_LINUX_LINUX_FS_CATS

/* ****** ****** */

#include <linux/fs.h>

/* ****** ****** */

typedef struct inode inode_struct ;
typedef struct file file_struct ;
typedef struct super_block super_block_struct ;

/* ****** ****** */

#define atsctrb_linux_new_inode new_inode

/* ****** ****** */

#endif /* ATSCTRB_LINUX_LINUX_FS_CATS */

/* end of [fs.cats] */
