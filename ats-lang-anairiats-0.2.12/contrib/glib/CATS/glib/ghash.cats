/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
** All rights reserved
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

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATSCTRB_GLIB_GHASH_CATS
#define ATSCTRB_GLIB_GHASH_CATS

/* ****** ****** */

/*
#include "glib/ghash.h"
*/

/* ****** ****** */

typedef GHashTable *GHashTable_ref ;

/* ****** ****** */

#define atsctrb_g_hash_table_new g_hash_table_new
#define atsctrb_g_hash_table_destroy g_hash_table_destroy
#define atsctrb_g_hash_table_size g_hash_table_size
#define atsctrb_g_hash_table_insert g_hash_table_insert
#define atsctrb_g_hash_table_lookup hash_table_lookup

#define atsctrb_g_str_hash g_str_hash

/* ****** ****** */

#endif /* ATSCTRB_GLIB_GHASH_CATS */
