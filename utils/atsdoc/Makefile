#######################################################################
#                                                                     #
#                         Applied Type System                         #
#                                                                     #
#                              Hongwei Xi                             #
#                                                                     #
#######################################################################

#
# ATS/Postiats - Unleashing the Potential of Types!
# Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software
# All rights reserved
#
# ATS is  free software;  you can redistribute it and/or modify it under
# the  terms of the  GNU General Public License as published by the Free
# Software Foundation; either version 2.1, or (at your option) any later
# version.
# 
# ATS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
# for more details.
# 
# You  should  have  received  a  copy of the GNU General Public License
# along  with  ATS;  see the  file COPYING.  If not, please write to the
# Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.
#

######
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Start Time: July, 2011
#
######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

GCFLAG=-D_ATS_GCATS

######

ATSCCFLAGS=-g
ATSCCFLAGS=-g -O
ATSCCFLAGS=-g -O2

######

SOURCES := \
  atsdoc_translate.sats \
  atsdoc_translate.dats \
  atsdoc_translate_error.dats \
  atsdoc_translate_item.dats \

SOURCESsta := $(filter %.sats, $(SOURCES))
SOURCESdyn := $(filter %.dats, $(SOURCES))

######

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))

######

all:: atsdoc

######
#
atsdoc: \
atsdoc_main_dats.o $(OBJECTS) ; \
$(ATSCC) $(GCFLAG) $(ATSCCFLAGS) -o $@ $^ -latsdoc
#
######
#
atsdoc_ngc: \
atsdoc_main_dats.o $(OBJECTS) ; \
$(ATSCC) -D_ATS_NGC $(ATSCCFLAGS) -o $@ $^ -latsdoc
#
######

%_sats.o: %.sats; $(ATSCC) $(ATSCCFLAGS) -c $<
%_dats.o: %.dats; $(ATSCC) $(ATSCCFLAGS) -c $<

######
#
# HX: '-o .depend' means appending instead of overwriting
#
depend:: ; $(RMF) .depend
depend:: ; $(ATSOPT) -o .depend -dep1 -s $(SOURCESsta)
depend:: ; $(ATSOPT) -o .depend -dep1 -d $(SOURCESdyn)
depend:: ; $(ATSOPT) -o .depend -dep1 -d atsdoc_main.dats
#
-include .depend
#
######

RMF=rm -f
WCL=wc -l

######

srclines:: ; $(WCL) $(SOURCES)

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o
clean:: ; $(RMF) *_?ats.c

######

cleanall:: clean
cleanall:: ; $(RMF) atsdoc
cleanall:: ; $(RMF) atsdoc_ngc

###### end of [Makefile] ######
