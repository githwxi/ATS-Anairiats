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
checkall:: problem6-hwxi
checkall:: problem6-hwxi2

######

problem6-hwxi: problem6-hwxi.dats
	$(ATSCC) -O2 -o $@ $< && ./problem6-hwxi
problem6-hwxi2: problem6-hwxi2.dats
	$(ATSCC) -O2 -o $@ $< && ./problem6-hwxi2

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem6-hwxi
cleanall:: ; $(RMF) problem6-hwxi2
