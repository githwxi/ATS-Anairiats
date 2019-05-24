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

GVCFLAGS=`pkg-config libgvc --cflags`

GVLDFLAGS=`pkg-config libgvc --libs`

######

all::

######

cleanall:: clean

######

all:: test01 ; ./test01 < data/hashtable.gv
test01: graphviz-test01.dats
	$(ATSCC) -O2 -g -o $@ $(GVCFLAGS) $< $(GVLDFLAGS)
cleanall:: ; $(RMF) test01

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o

###### end of [Makefile] ######
