######
#
# A variety of examples involving dependent and/or linear types
#
######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif # end of [ifeq]

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

######

ATSCTRB=$(ATSHOME)/contrib/scripting/atsctrb_scripting.o

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean
cleanall:: ; $(RMF) *_?ats.html

######

checkall:: average
average: average.dats; $(ATSCC) -o average average.dats $(ATSCTRB) -lpcre && ./average
cleanall:: ; $(RMF) average

checkall:: linesplit
linesplit: linesplit.dats
	$(ATSCC) -o linesplit linesplit.dats $(ATSCTRB) -lpcre && ./linesplit < data/grades.txt
cleanall:: ; $(RMF) linesplit

checkall:: fsubst
fsubst: fsubst.dats
	$(ATSCC) -o fsubst fsubst.dats $(ATSCTRB) -lpcre && ./fsubst < data/grades.txt Ben Benjamin
cleanall:: ; $(RMF) fsubst

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_dats.c *_sats.c

###### end of [Makefile] ######
