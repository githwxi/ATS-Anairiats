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
XRCFLAGS=`pkg-config cairo --cflags`
GTKCFLAGS = `pkg-config gtk+-2.0 --cflags`

######

all:: atsctrb_atspslide.o
all:: clean

######

SOURCES := \
  dynloadall.dats \
  atspslide_cairodraw.dats \
  atspslide_glTexture.dats \

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))

######

atsctrb_atspslide.o: $(OBJECTS); ld -r -o $@ $^

######

######
#
dynloadall_dats.o: dynloadall.dats; $(ATSCC) -o $@ -c $<
#
# atspslide_sats.o: SATS/atspslide.sats; $(ATSCC) -o $@ -c $<
#
atspslide_cairodraw_dats.o: \
  DATS/atspslide_cairodraw.dats ; $(ATSCC) -o $@ $(XRCFLAGS) -c $<
atspslide_glTexture_dats.o: \
  DATS/atspslide_glTexture.dats ; $(ATSCC) -o $@ $(GTKCFLAGS) -c $<
#
######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c *_?ats.o

cleanall:: clean
cleanall:: ; $(RMF) atsctrb_atspslide.o

###### end of [Makefile] ######
