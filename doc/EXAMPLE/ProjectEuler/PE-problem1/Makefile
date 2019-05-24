#
# Time of Generation: Sat Dec 18 08:35:01 2010
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
checkall:: problem1-hwxi
checkall:: problem1-hwxi2

######

problem1-hwxi: problem1-hwxi.dats
	$(ATSCC) -O2 -o $@ $< && ./problem1-hwxi
problem1-hwxi2: problem1-hwxi2.dats
	$(ATSCC) -D_ATS_PROOFCHECK -O2 -o $@ $< && ./problem1-hwxi2

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem1-hwxi
cleanall:: ; $(RMF) problem1-hwxi2
