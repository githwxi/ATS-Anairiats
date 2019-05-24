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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

/* ****** ****** */
//
// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: October, 2011
//
/* ****** ****** */

#ifndef ATSCTRB_GTKGLEXT_GTK_CATS
#define ATSCTRB_GTKGLEXT_GTK_CATS

/* ****** ****** */

#include <gtk/gtkgl.h>

/* ****** ****** */

#define atsctrb_gtk_widget_is_gl_capable gtk_widget_is_gl_capable

#define atsctrb_gtk_widget_get_gl_config gtk_widget_get_gl_config

#define atsctrb_gtk_widget_get_gl_context gtk_widget_get_gl_context

#define atsctrb_gtk_widget_get_gl_drawable gtk_widget_get_gl_drawable

/* ****** ****** */

#endif // end of [ATSCTRB_GTKGLEXT_GTK_CATS]

/* end of [gtk.cats] */
