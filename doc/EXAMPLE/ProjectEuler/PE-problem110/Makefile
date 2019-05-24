#
# Time of Generation: Wed Dec 15 14:30:50 2010
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
checkall:: problem110-hwxi

######

problem110-hwxi: problem110-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lm && ./problem110-hwxi

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem110-hwxi
