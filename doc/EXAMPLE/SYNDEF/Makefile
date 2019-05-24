#
#
# Some examples in ATS involving syndef-loaded identifiers
#
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ($"(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.5"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt
ATSOPT=$(ATSLIBQ)/src/atsopt

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
html::
xref::

######

checkall:: fact
fact: fact_dats.c
	$(ATSCC) -o fact fact_dats.c -lats && ./fact
fact_dats.c: fact.dats
	$(ATSOPT) -o $@ -d $<

checkall:: forlist
forlist: forlist_dats.c
	$(ATSCC) -o forlist forlist_dats.c -lats && ./forlist
forlist_dats.c: forlist.dats
	$(ATSOPT) -o $@ -d $<

checkall:: forrange
forrange: forrange_dats.c
	$(ATSCC) -o forrange forrange_dats.c -lats && ./forrange
forrange_dats.c: forrange.dats
	$(ATSOPT) -o $@ -d $<

checkall:: multable
multable: multable_dats.c
	$(ATSCC) -o multable multable_dats.c -lats && ./multable
multable_dats.c: multable.dats
	$(ATSOPT) -o $@ -d $<

######

html:: ; $(ATSOPT) --posmark_html -d fact.dats > fact_dats.html
html:: ; $(ATSOPT) --posmark_html -d forlist.dats > forlist_dats.html
html:: ; $(ATSOPT) --posmark_html -d forrange.dats > forrange_dats.html
html:: ; $(ATSOPT) --posmark_html -d multable.dats > multable_dats.html

######

xref:: ; $(ATSOPT) --posmark_xref=XREF -d \
  $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
xref:: ; $(ATSOPT) --posmark_xref=XREF -d fact.dats > fact_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d forlist.dats > forlist_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d forrange.dats > forrange_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d multable.dats > multable_dats.html

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) ./INTRO/*
	$(RMF) *_dats.c *_sats.c

cleanall:: clean
	$(RMF) ./XREF/*
	$(RMF) *_?ats.html
	$(RMF) fact
	$(RMF) forlist
	$(RMF) forrange
	$(RMF) multable

###### end of [Makefile] ######
