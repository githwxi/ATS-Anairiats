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
checkall:: problem2-hwxi
checkall:: problem2-hwxi2

######

problem2-hwxi: problem2-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp && ./problem2-hwxi
problem2-hwxi2: problem2-hwxi2.dats
	$(ATSCC) -D_ATS_PROOFCHECK -O2 -o $@ $< && ./problem2-hwxi2

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem2-hwxi
cleanall:: ; $(RMF) problem2-hwxi2
