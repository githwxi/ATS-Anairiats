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
checkall:: problem16-hwxi
checkall:: problem16-hwxi2

######

problem16-hwxi: problem16-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./problem16-hwxi
problem16-hwxi2: problem16-hwxi2.dats
	$(ATSCC) -O2 -o $@ $< && ./problem16-hwxi2

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem16-hwxi
cleanall:: ; $(RMF) problem16-hwxi2
