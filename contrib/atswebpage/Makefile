#
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: August, 2011
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif # end of [ifeq]

######

ATSCC=$(ATSUSRQ)/bin/atscc -Wall

######

all:: atsctrb_atswebpage.o
all:: clean

######

SOURCES := \
  dynloadall.dats \
  weboxlayout.sats weboxlayout.dats \

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))

######

atsctrb_atswebpage.o: $(OBJECTS); ld -r -o $@ $^

######

dynloadall_dats.o: dynloadall.dats; $(ATSCC) -o $@ -c $<
weboxlayout_sats.o: SATS/weboxlayout.sats; $(ATSCC) -o $@ -c $<
weboxlayout_dats.o: DATS/weboxlayout.dats; $(ATSCC) -o $@ -c $<

######

clean::
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f atsctrb_atswebpage.o

###### end of [Makefile] ######
