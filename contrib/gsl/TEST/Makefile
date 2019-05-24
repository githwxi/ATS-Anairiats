#
# A simple Makefile
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.6"
endif # end of [ifeq]

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSLIBQ)/contrib/GL/atsctrb_graphviz.o

######

LDFLAGS=-lgsl -lgslcblas

######

all::

######

cleanall:: clean

######

all:: test_rng ; ./test_rng
test_rng: test_rng.dats ; $(ATSCC) -O2 -o $@ $< $(LDFLAGS) 
cleanall:: ; $(RMF) test_rng

all:: test_randist ; ./test_randist
test_randist: test_randist.dats ; $(ATSCC) -O2 -o $@ $< $(LDFLAGS) 
cleanall:: ; $(RMF) test_randist

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o

###### end of [Makefile] ######
