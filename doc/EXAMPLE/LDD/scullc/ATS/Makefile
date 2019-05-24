#
# A simple Makefile
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

scullc_dats.c: scullc.dats scullc.sats ; $(ATSCC) -cc -o ../$@ $<
scullc_data_dats.c: scullc_data.dats scullc.sats ; $(ATSCC) -cc -o ../$@ $<

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) scullc_dats.c

cleanall:: clean

###### end of [Makefile]
