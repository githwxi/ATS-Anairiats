#
# A simple make file
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all

all: checkall cleanall

######

checkall:: test1 test2

######

test1: test1.dats
	$(ATSCC) -o $@ test1.dats enigma.sats enigma.dats && ./test1
cleanall:: ; $(RMF) test1

test2: test2.dats
	$(ATSCC) -o $@ test2.dats enigma.sats enigma.dats && ./test2 < test2.dats
cleanall:: ; $(RMF) test2

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean

###### end of [Makefile] ######