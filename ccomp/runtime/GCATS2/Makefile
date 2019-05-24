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
## Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
## Time: October 2009

## ###### ###### ##

GCC=gcc
ATSCC=$(ATSHOME)/bin/atscc
ATSCCFLAGS= -Wall -g # -m64
ATSOPT=$(ATSHOME)/bin/atsopt

######

SOURCES := \
  gcats2.sats \
  gcats2_top.dats \
  gcats2_misc.dats \
  gcats2_freeitmlst.dats \
  gcats2_chunk.dats \
  gcats2_pointer.dats \
  gcats2_globalrts.dats \
  gcats2_marking.dats \
  gcats2_collecting.dats \
  gcats2_autmem.dats \
  gcats2_manmem.dats \

TARGETS := $(patsubst %.sats, %_sats.c, $(SOURCES))
TARGETS := $(patsubst %.dats, %_dats.c, $(TARGETS))
TARGETS_mt := $(TARGETS) gcats2_multithread_dats.c

######

gc.o: \
  gcats2_hats $(TARGETS)
	$(ATSCC) $(ATSCCFLAGS) -c -o gc.o -x c gcats2_all.cats

gc_mt.o: \
  gcats2_mt_hats $(TARGETS_mt)
	$(ATSCC) $(ATSCCFLAGS) -D_ATS_MULTITHREAD -c -o gc_mt.o -x c gcats2_all.cats

######

gcats2_hats: gcats2_master.hats
	$(GCC) -E -P -D_CHEADER -o gcats2_c.h -x c gcats2_master.hats
	$(GCC) -E -P -D_ATSHEADER -o gcats2_ats.hats -x c gcats2_master.hats

gcats2_mt_hats: gcats2_master.hats
	$(GCC) -E -P \
          -D_ATS_MULTITHREAD -D_CHEADER  -o gcats2_c.h -x c gcats2_master.hats
	$(GCC) -E -P \
          -D_ATS_MULTITHREAD -D_ATSHEADER -o gcats2_ats.hats -x c gcats2_master.hats

######

gcats2_sats.c: gcats2.sats
	$(ATSOPT) -o $@ --static gcats2.sats

gcats2_top_dats.c: gcats2_top.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_top.dats

gcats2_misc_dats.c: gcats2_misc.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_misc.dats

gcats2_freeitmlst_dats.c: gcats2_freeitmlst.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_freeitmlst.dats

gcats2_chunk_dats.c: gcats2_chunk.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_chunk.dats

gcats2_pointer_dats.c: gcats2_pointer.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_pointer.dats

gcats2_globalrts_dats.c: gcats2_globalrts.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_globalrts.dats

gcats2_marking_dats.c: gcats2_marking.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_marking.dats

gcats2_collecting_dats.c: gcats2_collecting.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_collecting.dats

gcats2_autmem_dats.c: gcats2_autmem.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_autmem.dats

gcats2_manmem_dats.c: gcats2_manmem.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_manmem.dats

gcats2_multithread_dats.c: gcats2_multithread.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_multithread.dats

######

test: gcats2_hats gcats2_test_dats.c $(TARGETS)
	$(ATSCC) $(ATSCCFLAGS) -o test gcats2_test_dats.c $(TARGETS) \
      && ./test \
      && rm -f ./test

gcats2_test_dats.c: gcats2_test.dats
	$(ATSOPT) --pervasive gcats2_ats.hats -o $@ --dynamic gcats2_test.dats

######

clean::
	rm -f gcats2_c.h
	rm -f gcats2_ats.hats
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f *.o test

###### end of [Makefile] ######
