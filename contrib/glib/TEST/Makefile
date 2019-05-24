#
#
# A simple Makefile for some glib testing code
#
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.3"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSLIBQ)/contrib/glib/atsctrb_glib.o

######

GLIBCFLAGS=`pkg-config glib-2.0 --cflags`

######

.PHONY: all

######

all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: garray-test
garray-test: garray-test.dats
	$(ATSCC) -O3 $(GLIBCFLAGS) -o $@ $< $(ATSCTRB) -lglib-2.0 && ./$@
cleanall:: ; $(RMF) garray-test

######

checkall:: glist-test
glist-test: glist-test.dats
	$(ATSCC) -O3 $(GLIBCFLAGS) -o $@ $< $(ATSCTRB) -lglib-2.0 && ./$@
cleanall:: ; $(RMF) glist-test

######

checkall:: gqsort-test
gqsort-test: gqsort-test.dats
	$(ATSCC) -O3 $(GLIBCFLAGS) -o $@ $< $(ATSCTRB) -lglib-2.0 && ./$@
cleanall:: ; $(RMF) gqsort-test

######

checkall:: gstring-test
gstring-test: gstring-test.dats
	$(ATSCC) -O3 $(GLIBCFLAGS) -o $@ $< $(ATSCTRB) -lglib-2.0 && ./$@
cleanall:: ; $(RMF) gstring-test

######

checkall:: gunicode-test
gunicode-test: gunicode-test.dats
	$(ATSCC) -O3 $(GLIBCFLAGS) -o $@ $< $(ATSCTRB) -lglib-2.0 && ./$@
cleanall:: ; $(RMF) gunicode-test

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
