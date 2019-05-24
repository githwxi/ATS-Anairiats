#
# Time of Generation: Wed Dec 15 14:30:49 2010
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif
ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

######

.PHONY: all
all:: checkall
all:: cleanall
checkall:: problem20-hwxi
checkall:: problem20-hwxi2

######

problem20-hwxi: problem20-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./problem20-hwxi
problem20-hwxi2: problem20-hwxi2.dats
	$(ATSCC) -O2 -o $@ $< && ./problem20-hwxi2

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem20-hwxi
cleanall:: ; $(RMF) problem20-hwxi2
