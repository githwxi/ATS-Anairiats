#########################################################################
#                                                                       #
#                         Applied Type System                           #
#                                                                       #
#                              Hongwei Xi                               #
#                                                                       #
#########################################################################

#
#  ATS - Unleashing the Power of Types!
#
#  Copyright (C) 2002-2010 Hongwei Xi.
#
#  ATS is free software;  you can  redistribute it and/or modify it under
#  the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
#  Free Software Foundation; either version 2.1, or (at your option)  any
#  later version.
# 
#  ATS is distributed in the hope that it will be useful, but WITHOUT ANY
#  WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
#  FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
#  for more details.
# 
#  You  should  have  received  a  copy of the GNU General Public License
#  along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
#  Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
#  02110-1301, USA.
#

#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCCFLAGS=
ATSRUNTIME=$(ATSHOMEQ)/ccomp/runtime
IATS=-IATS $(ATSHOMEQ)/src

CCFLAGS=-fPIC -O2
INCLUDES=-I$(ATSHOMEQ)

######

SOURCES = \
  atsyndef_util.sats \
  atsyndef_util.dats \
  atsyndef_main.sats \
  atsyndef_main.dats \
  atsyndef_FOR.dats \
  atsyndef_ARRAY.dats \

OBJECTS := $(patsubst %.sats, %_sats.o, $(SOURCES))
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))

######

ATSLIB=$(ATSHOMEQ)/ccomp/lib
ATSLIB=$(ATSHOMEQ)/ccomp/lib64

######

all:: libatsyndef
all:: cleanall

######

libatsyndef: $(OBJECTS)
	$(ATSCC) -fPIC -shared -o $(ATSLIB)/libatsyndef.so -Wl,-soname,libatsyndef.so `ar t libatsyndef.a`

######

AR=ar

######

atsyndef_util_sats.o: atsyndef_util.sats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_util.sats
	$(AR) -r libatsyndef.a $@
atsyndef_util_dats.o: atsyndef_util.dats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_util.dats
	$(AR) -r libatsyndef.a $@

atsyndef_main_sats.o: atsyndef_main.sats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_main.sats
	$(AR) -r libatsyndef.a $@
atsyndef_main_dats.o: atsyndef_main.dats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_main.dats
	$(AR) -r libatsyndef.a $@

######

atsyndef_FOR_dats.o: atsyndef_FOR.dats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_FOR.dats
	$(AR) -r libatsyndef.a $@

atsyndef_ARRAY_dats.o: atsyndef_ARRAY.dats
	$(ATSCC) $(IATS) $(CCFLAGS) -c atsyndef_ARRAY.dats
	$(AR) -r libatsyndef.a $@

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) libatsyndef.a

distclean:: cleanall

###### end of [Makefile] ######
