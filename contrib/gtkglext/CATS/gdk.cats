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

#ifndef ATSCTRB_GTKGLEXT_GDK_CATS
#define ATSCTRB_GTKGLEXT_GDK_CATS

/* ****** ****** */

#include <gdk/gdkgl.h>

/* ****** ****** */

#define atsctrb_gdk_gl_config_new_by_mode gdk_gl_config_new_by_mode

/* ****** ****** */

#define atsctrb_gdk_gl_context_destroy gdk_gl_context_destroy
#define atsctrb_gdk_gl_context_get_gl_drawable gdk_gl_context_get_gl_drawable
#define atsctrb_gdk_gl_context_get_gl_config gdk_gl_context_get_gl_config
#define atsctrb_gdk_gl_context_get_gl_share_list gdk_gl_context_get_gl_share_list

#define atsctrb_gdk_gl_context_is_direct gdk_gl_context_is_direct
#define atsctrb_gdk_gl_context_get_render_type gdk_gl_context_get_render_type

/* ****** ****** */

#define atsctrb_gdk_gl_drawable_is_double_buffered gdk_gl_drawable_is_double_buffered
#define atsctrb_gdk_gl_drawable_swap_buffers gdk_gl_drawable_swap_buffers

#define atsctrb_gdk_gl_drawable_gl_begin gdk_gl_drawable_gl_begin
#define atsctrb_gdk_gl_drawable_gl_end gdk_gl_drawable_gl_end

#define atsctrb_gdk_gl_drawable_get_size gdk_gl_drawable_get_size

/* ****** ****** */

#endif // end of [ATSCTRB_GTKGLEXT_GDK_CATS]

/* end of [gdk.cats] */
