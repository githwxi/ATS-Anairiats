#
# API for zeromq in ATS
#
# Start Time: December, 2012
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

ATSHOMEQ="$(ATSHOME)"

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCTRB=$(ATSHOMEQ)/contrib

######

all::

######

all:: atsctrb_zeromq.o
atsctrb_zeromq.o: zmq_dats.o ; ld -r -o $@ $^

######

zmq_dats.o: DATS/zmq.dats
	$(ATSCC) -O2 -I$(ATSCTRB) -IATS$(ATSCTRB) -o $@ -c $<

######

RMF=rm -f

######

all:: clean
clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c *_?ats.o

######

cleanall:: clean
cleanall:: ; $(RMF) atsctrb_zeromq.o

###### end of [Makefile] ######
