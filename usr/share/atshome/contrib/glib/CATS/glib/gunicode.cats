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

#ifndef ATSCTRB_GLIB_GUNICODE_CATS
#define ATSCTRB_GLIB_GUNICODE_CATS

/* ****** ****** */

/*
#include "glib/gunicode.h"
*/

/* ****** ****** */

#define atsctrb_g_unichar_isalnum g_unichar_isalnum
#define atsctrb_g_unichar_isalpha g_unichar_isalpha
#define atsctrb_g_unichar_iscntrl g_unichar_iscntrl
#define atsctrb_g_unichar_isdigit g_unichar_isdigit
#define atsctrb_g_unichar_isgraph g_unichar_isgraph
#define atsctrb_g_unichar_islower g_unichar_islower
#define atsctrb_g_unichar_isprint g_unichar_isprint
#define atsctrb_g_unichar_ispunct g_unichar_ispunct
#define atsctrb_g_unichar_isspace g_unichar_isspace
#define atsctrb_g_unichar_isupper g_unichar_isupper
#define atsctrb_g_unichar_isxdigit g_unichar_isxdigit
#define atsctrb_g_unichar_istitle g_unichar_istitle
#define atsctrb_g_unichar_isdefined g_unichar_isdefined
#define atsctrb_g_unichar_iswide g_unichar_iswide
#define atsctrb_g_unichar_iswide_cjk g_unichar_iswide_cjk
#define atsctrb_g_unichar_iszerowidth g_unichar_iszerowidth
#define atsctrb_g_unichar_ismark g_unichar_ismark

/* ****** ****** */

ATSinline()
glong
atsctrb_g_utf8_strlen_cstr
  (ats_ptr_type str) {
  return g_utf8_strlen ((gchar*)str, -1) ;
} // end of [atsctrb_g_utf8_strlen_cstr]
#define atsctrb_g_utf8_strlen_carr g_utf8_strlen

/* ****** ****** */

#endif /* ATSCTRB_GLIB_GUNICODE_CATS */
