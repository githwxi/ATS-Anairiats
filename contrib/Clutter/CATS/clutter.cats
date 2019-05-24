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
// Starting time: June, 2010
//
/* ****** ****** */

#ifndef ATSCTRB_CLUTTER_CATS
#define ATSCTRB_CLUTTER_CATS

/* ****** ****** */

#include <clutter/clutter.h>

/* ****** ****** */

//
// source: clutter-action.h
//

#define atsctrb_clutter_actor_add_action clutter_actor_add_action
#define atsctrb_clutter_actor_remove_action clutter_actor_remove_action
#define atsctrb_clutter_actor_clear_actions clutter_actor_clear_actions

/* ****** ****** */

//
// source: clutter-actor.h
//

#define atsctrb_clutter_actor_show clutter_actor_show
#define atsctrb_clutter_actor_show_all clutter_actor_show_all

#define atsctrb_clutter_actor_hide clutter_actor_hide
#define atsctrb_clutter_actor_hide_all clutter_actor_hide_all

#define atsctrb_clutter_actor_map clutter_actor_map
#define atsctrb_clutter_actor_unmap clutter_actor_unmap

#define atsctrb_clutter_actor_realize clutter_actor_realize
#define atsctrb_clutter_actor_unrealize clutter_actor_unrealize

/* ****** ****** */

#define atsctrb_clutter_actor_paint clutter_actor_paint
#define atsctrb_clutter_actor_queue_redraw clutter_actor_queue_redraw
#define atsctrb_clutter_actor_queue_relayout clutter_actor_queue_relayout

/* ****** ****** */

#define atsctrb_clutter_actor_get_width clutter_actor_get_width
#define atsctrb_clutter_actor_set_width clutter_actor_set_width
#define atsctrb_clutter_actor_get_height clutter_actor_get_height
#define atsctrb_clutter_actor_set_height clutter_actor_set_height
#define atsctrb_clutter_actor_get_size clutter_actor_get_size
#define atsctrb_clutter_actor_set_size clutter_actor_set_size
#define atsctrb_clutter_actor_get_position clutter_actor_get_position
#define atsctrb_clutter_actor_set_position clutter_actor_set_position

/* ****** ****** */

//
// source: clutter-color.h
//

#define atsctrb_clutter_color_new clutter_color_new
#define atsctrb_clutter_color_copy clutter_color_copy
#define atsctrb_clutter_color_free clutter_color_free

/* ****** ****** */

//
// source: clutter-container.h
//

#define atsctrb_clutter_container_add_actor clutter_container_add_actor

/* ****** ****** */

//
// source: clutter-main.h
//

#define atsctrb_clutter_main clutter_main
#define atsctrb_clutter_main_quit clutter_main_quit
#define atsctrb_clutter_main_level clutter_main_level

/* ****** ****** */

//
// source: clutter-rectangle.h
//

ATSinline()
ats_ptr_type
atsctrb_clutter_rectangle_new () {
  ClutterActor *actor = clutter_rectangle_new() ;
  g_object_ref_sink(G_OBJECT(actor)) ; // removing floating reference!
  return actor ;
} // end of [clutter_rectangle_new]

ATSinline()
ats_ptr_type
atsctrb_clutter_rectangle_new_with_color
  (ats_ptr_type clr) {
  ClutterActor *actor = clutter_rectangle_new_with_color((ClutterColor*)clr) ;
  g_object_ref_sink(G_OBJECT(actor)) ; // removing floating reference!
  return actor ;
} // end of [clutter_rectangle_new_with_color]

#define atsctrb_clutter_rectangle_get_color clutter_rectangle_get_color
#define atsctrb_clutter_rectangle_set_color clutter_rectangle_set_color

/* ****** ****** */

//
// source: clutter-stage.h
//

#define atsctrb_clutter_stage_get_default clutter_stage_get_default
#define atsctrb_clutter_stage_new clutter_stage_new
#define atsctrb_clutter_stage_is_default clutter_stage_is_default

#define atsctrb_clutter_stage_get_color clutter_stage_get_color
#define atsctrb_clutter_stage_set_color clutter_stage_set_color

#define atsctrb_clutter_stage_get_fullscreen clutter_stage_get_fullscreen
#define atsctrb_clutter_stage_set_fullscreen clutter_stage_set_fullscreen

#define atsctrb_clutter_stage_show_cursor clutter_stage_show_cursor
#define atsctrb_clutter_stage_hide_cursor clutter_stage_hide_cursor

#define atsctrb_clutter_stage_get_title clutter_stage_get_title
#define atsctrb_clutter_stage_set_title clutter_stage_set_title

/* ****** ****** */

#endif // end of [ATSCTRB_CLUTTER_CATS]

/* end of [clutter.cats] */
