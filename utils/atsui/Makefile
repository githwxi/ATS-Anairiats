#########################################################################
##                                                                     ##
##                         Applied Type System                         ##
##                                                                     ##
##                              Hongwei Xi                             ##
##                                                                     ##
#########################################################################

##
## ATS/Anairiats - Unleashing the Power of Types!
##
## Copyright (C) 2010-201? Hongwei Xi, Boston University
##
## All rights reserved
##
## ATS is  free software;  you can redistribute it and/or modify it under
## the  terms of the  GNU General Public License as published by the Free
## Software Foundation; either version 2.1, or (at your option) any later
## version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

## ###### ###### ##

## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: April 2010

######

MAKE=make

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCCFLAGS=-g

######

GTKLIBS=`pkg-config gtk+-2.0 --libs`
GTKCFLAGS=`pkg-config gtk+-2.0 --cflags`

## CAIROCFLAGS= ...
## PANGOCFLAGS= `pkg_config pango --cflags`

CCFLAGS =$(GTKCFLAGS)

######

SOURCES := \
  atsui_util.sats atsui_util.dats \
  atsui_compile.dats \
  atsui_menu_file.dats \
  atsui_menuitem_file_openfile.dats \
  atsui_menuitem_file_save.dats \
  atsui_menuitem_file_saveas.dats \
  atsui_menuitem_file_quit.dats \
  atsui_menu_edit.dats \
  atsui_menuitem_edit_undoredo.dats \
  atsui_menu_view.dats \
  atsui_menuitem_view_fontsel.dats \
  atsui_menu_winlst.dats \
  atsui_textview_source.dats \
  atsui_textview_source_linenumber.dats \
  atsui_textview_output.dats \
  atsui_srcwinlst.sats atsui_srcwinlst.dats \
  atsui_topenv.sats atsui_topenv.dats \

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))

######

atsui: \
  atsui_main_dats.o \
  $(OBJECTS)
	$(ATSCC) \
  $(ATSCCFLAGS) $(CCFLAGS) \
  -o atsui \
  atsui_main_dats.o \
  $(OBJECTS) \
  $(ATSGTKLIB) \
  $(GTKLIBS) \

######

ATSGTKLIB=$(ATSHOMEQ)/contrib/GTK/atsctrb_GTK.o
atsui_main_dats.o: atsui_main.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_main.dats

######

atsui_util_sats.o: atsui_util.sats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_util.sats

atsui_util_dats.o: atsui_util.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_util.dats

######

atsui_srcwinlst_sats.o: atsui_srcwinlst.sats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_srcwinlst.sats

atsui_srcwinlst_dats.o: atsui_srcwinlst.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_srcwinlst.dats

######

atsui_menu_file_dats.o: atsui_menu_file.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menu_file.dats

atsui_menuitem_file_openfile_dats.o: atsui_menuitem_file_openfile.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menuitem_file_openfile.dats

atsui_menuitem_file_save_dats.o: atsui_menuitem_file_save.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menuitem_file_save.dats

atsui_menuitem_file_saveas_dats.o: atsui_menuitem_file_saveas.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menuitem_file_saveas.dats

atsui_menuitem_file_quit_dats.o: atsui_menuitem_file_quit.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menuitem_file_quit.dats

######

atsui_menu_edit_dats.o: atsui_menu_edit.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menu_edit.dats

atsui_menuitem_edit_undoredo_dats.o: atsui_menuitem_edit_undoredo.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menuitem_edit_undoredo.dats

######

atsui_menu_view_dats.o: atsui_menu_view.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menu_view.dats

atsui_menuitem_view_fontsel_dats.o: atsui_menuitem_view_fontsel.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menuitem_view_fontsel.dats

######

atsui_menu_winlst_dats.o: atsui_menu_winlst.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_menu_winlst.dats

######

atsui_compile_dats.o: atsui_compile.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_compile.dats

######

atsui_textview_source_dats.o: atsui_textview_source.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_textview_source.dats

atsui_textview_source_linenumber_dats.o: atsui_textview_source_linenumber.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_textview_source_linenumber.dats

atsui_textview_output_dats.o: atsui_textview_output.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_textview_output.dats

######

atsui_topenv_sats.o: atsui_topenv.sats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_topenv.sats

atsui_topenv_dats.o: atsui_topenv.dats
	$(ATSCC) $(ATSCCFLAGS) $(CCFLAGS) -c atsui_topenv.dats

######

clean::
	rm -f *~
	rm -f *_?ats.c  *_?ats.o

cleanall: clean
	rm -f atsui

######

## end of [Makefile] ##

######
