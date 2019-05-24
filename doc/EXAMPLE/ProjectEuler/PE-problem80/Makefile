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
checkall:: problem80-hwxi

######

problem80-hwxi: problem80-hwxi.dats
	$(ATSCC) -O2 -o $@ $< -lats -lgmp -lm && ./problem80-hwxi

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean
cleanall:: ; $(RMF) problem80-hwxi
