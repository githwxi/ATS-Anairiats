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
checkall:: problem15-hwxi
checkall:: problem15-hwxi2
checkall:: problem15-mberndt

######

problem15-hwxi: problem15-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./problem15-hwxi
problem15-hwxi2: problem15-hwxi2.dats
	$(ATSCC) -O2 -o $@ $< && ./problem15-hwxi2
problem15-mberndt: problem15-mberndt.dats
	$(ATSCC) -O2 -o $@ $< && ./problem15-mberndt

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem15-hwxi
cleanall:: ; $(RMF) problem15-hwxi2
cleanall:: ; $(RMF) problem15-mberndt
