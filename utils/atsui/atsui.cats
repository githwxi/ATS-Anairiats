/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2010-201? Hongwei Xi, Boston University
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
// Time: April 2010

/* ****** ****** */

#ifndef ATSUI_CATS
#define ATSUI_CATS

/* ****** ****** */

typedef
struct {
  GtkWindow *topwin ; // this is the toplevel main window
  GtkAccelGroup *aclgrp ; // this is the accelgroup associated with the topwin
//
  GtkVBox *vbox0 ; // this is the immediate vbox inside topwin
//
  GtkMenu *menu_file ; // this is the FILE menu
  GtkMenuItem *menuitem_file_close ; // this is the CLOSE item in the FILE menu
  GtkMenuItem *menuitem_file_save ; // this is the SAVE item in the FILE menu
  GtkMenuItem *menuitem_file_saveas ; // this is the SAVEAS item in the FILE menu
//
  // GtkMenu *menu_edit ; // this is the EDIT menu
  GtkMenuItem *menuitem_edit_undo ; // this is the UNDO item in the EDIT menu
  GtkMenuItem *menuitem_edit_redo ; // this is the REDO item in the EDIT menu
  GtkMenuItem *menuitem_edit_cut ; // this is the CUT item in the EDIT menu
  GtkMenuItem *menuitem_edit_copy ; // this is the COPY item in the EDIT menu
  GtkMenuItem *menuitem_edit_paste ; // this is the PASTE item in the EDIT menu
//
  // GtkMenu *menu_view ; // this is the VIEW menu
  GtkMenuItem *menuitem_view_fontsel ; // this is the FONT item in the VIEW menu
  GtkMenuItem *menuitem_view_linenumber ; // this is the LINE NUMBERS item in the VIEW menu
//
  GtkMenu *menu_window ; // this the WINDOW LIST menu
//
  GtkFrame *container_source ; // for containing textview_source
  GtkTextView *textview_source ; // for source code manipulation
//
  GtkContainer *container_output ; // for containing textview_output
  GtkTextView *textview_output ; // for compilation output
//
  GtkStatusbar *statusbar ; // for various minor information
//
} ATSUItopenv ;

extern ATSUItopenv theATSUItopenv ;

/* ****** ****** */

#endif

/* end of [atsui.cats] */
