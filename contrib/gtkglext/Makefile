#
# API for gtkglext in ATS
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: October, 2011
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSUSRQ)/contrib
GTKGLEXTCFLAGS=`pkg-config --cflags --libs gtk+-2.0 gtkglext-1.0 gtkglext-x11-1.0`

######

all:: atsctrb_gtkglext.o
all:: clean

######

atsctrb_gtkglext.o: gdk_dats.o gtk_dats.o ; ld -r -o $@ $^

######

gdk_dats.o: DATS/gdk.dats
	$(ATSCC) -Wall -I$(ATSCTRB) -IATS$(ATSCTRB) $(GTKGLEXTCFLAGS) -c $<
gtk_dats.o: DATS/gtk.dats
	$(ATSCC) -Wall -I$(ATSCTRB) -IATS$(ATSCTRB) $(GTKGLEXTCFLAGS) -c $<

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c *_?ats.o

cleanall:: clean
cleanall:: ; $(RMF) atsctrb_gtkglext.o

###### end of [Makefile] ######
