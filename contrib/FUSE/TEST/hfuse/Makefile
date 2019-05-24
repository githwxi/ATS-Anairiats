#
# A simple Makefile for FUSE tests
#

######

ATSHOMEQ="$(ATSHOME)"
ATSRUNTIME=$(ATSHOME)/ccomp/runtime
ATSLIB=$(ATSHOME)/ccomp/lib
ATSCC=$(ATSHOMEQ)/bin/atscc
FUSEFLAGS=`pkg-config fuse --cflags --libs`
CC=gcc

######

.PHONY: all
all:: checkall

######

checkall:: compall cleanall

compall:: \

######

hfuse_dats.o: hfuse.dats
	$(ATSCC) -c -D_ATS_PRELUDE_NONE $(FUSEFLAGS) $< -Wall -g -O2 -o $@ 

######

clean::
	rm -f *~
	rm -f *_?ats.c
	rm -f *_?ats.o

cleanall: clean
	rm -f hfuse_?ats.o

###### end of [Makefile] ######
