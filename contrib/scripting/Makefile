#
# for simple scripting
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: January, 2011
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif # end of [ifeq]

######

ATSCC=$(ATSUSRQ)/bin/atscc -Wall

######

all: atsctrb_scripting.o clean

######

atsctrb_scripting.o: scripting_dats.o; ld -r -o $@ $^

######

scripting_dats.o: DATS/scripting.dats
	$(ATSCC) $(XRCFLAGS) -o $@ -c DATS/scripting.dats

######

clean::
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f atsctrb_scripting.o

###### end of [Makefile] ######
