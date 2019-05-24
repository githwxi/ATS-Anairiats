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
** Copyright (C) 2009-2010 Hongwei Xi.
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

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: June, 2010

/* ****** ****** */

#ifndef ATSCTRB_CURL_CATS
#define ATSCTRB_CURL_CATS

/* ****** ****** */

#include "curl/curl.h"

/* ****** ****** */

#define atsctrb_curl_global_init curl_global_init
#define atsctrb_curl_global_cleanup curl_global_cleanup

/* ****** ****** */

#define atsctrb_curl_easy_init curl_easy_init
#define atsctrb_curl_easy_setopt curl_easy_setopt
#define atsctrb_curl_easy_perform curl_easy_perform
#define atsctrb_curl_easy_cleanup curl_easy_cleanup

/* ****** ****** */

#define atsctrb_curl_easy_getinfo curl_easy_getinfo

/* ****** ****** */

#define atsctrb_curl_easy_duphandle curl_easy_duphandle

/* ****** ****** */

#endif // ATSCTRB_CURL_CATS

/* ****** ****** */

/* end of [curl.cats] */
