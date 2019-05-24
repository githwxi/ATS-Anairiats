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
  hello \

######

hello: hello.dats
	$(ATSCC) \
  -D_ATS_PRELUDE_NONE $(FUSEFLAGS) hello.dats \
  -Wall -g -O2 -o hello -lats -lfuse -pthread -lrt -ldl

######

clean::
	rm -f *~
	rm -f *_?ats.c
	rm -f *_?ats.o

cleanall: clean
	rm -f hello hello.o

###### end of [Makefile] ######
