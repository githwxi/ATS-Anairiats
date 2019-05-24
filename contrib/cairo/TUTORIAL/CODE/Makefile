#
# A simple Makefile
#

######

ATSHOMEQ = "$(ATSHOME)"
ATSCC = $(ATSHOMEQ)/bin/atscc
ATSOPT = $(ATSHOMEQ)/bin/atsopt
ATSDOC = $(ATSHOMEQ)/bin/atsdoc

######

all:: tutprog_hw.dats
all:: tutprog_hw.dats.extract
all:: tutprog_hw.png

all:: tutprog_linecap.png
all:: tutprog_linejoin.png

all:: tutprog_triangle.dats
all:: tutprog_triangle.dats.extract
all:: tutprog_triangle

all:: tutprog_sqrcirc.png
all:: illucircmot.png
all:: illuwavy.png

all:: tutprog_showtext.png

all:: clean

######

tutprog_hw0: tutprog_hw_atxt.dats
	$(ATSCC) -o $@ $< -latsdoc
tutprog_hw1: tutprog_hw_atxt.dats
	$(ATSCC) -DATS ISEXTRACT -o $@ $< -latsdoc
tutprog_hw_atxt.dats: tutprog_hw.atxt
	$(ATSDOC) --outcode $@ -i $< > tutprog_hw_atxt.txt

tutprog_hw.dats: tutprog_hw0; ./$< > $@
tutprog_hw.dats.extract: tutprog_hw1; ./$< > $@

tutprog_hw.png: tutprog_hw ; ./$<
tutprog_hw: tutprog_hw.dats
	$(ATSCC) -o $@ $< `pkg-config cairo --cflags --libs`

clean:: ; $(RMF) tutprog_hw
clean:: ; $(RMF) tutprog_hw0
clean:: ; $(RMF) tutprog_hw1

cleanall:: ; $(RMF) tutprog_hw.dats
cleanall:: ; $(RMF) tutprog_hw.dats.extract
cleanall:: ; $(RMF) tutprog_hw.png

######

tutprog_linecap: tutprog_linecap.dats
	$(ATSCC) -o $@ $< `pkg-config cairo --cflags --libs`
tutprog_linecap.png: tutprog_linecap ; ./$<
clean:: ; $(RMF) tutprog_linecap
cleanall:: ; $(RMF) tutprog_linecap.png

tutprog_linejoin: tutprog_linejoin.dats
	$(ATSCC) -o $@ $< `pkg-config cairo --cflags --libs`
tutprog_linejoin.png: tutprog_linejoin ; ./$<
clean:: ; $(RMF) tutprog_linejoin
cleanall:: ; $(RMF) tutprog_linejoin.png

######

tutprog_triangle0: tutprog_triangle_atxt.dats
	$(ATSCC) -o $@ $< -latsdoc
tutprog_triangle1: tutprog_triangle_atxt.dats
	$(ATSCC) -DATS ISEXTRACT -o $@ $< -latsdoc
tutprog_triangle_atxt.dats: tutprog_triangle.atxt
	$(ATSDOC) --outcode $@ -i $< > tutprog_triangle_atxt.txt

tutprog_triangle.dats: tutprog_triangle0; ./$< > $@
tutprog_triangle.dats.extract: tutprog_triangle1; ./$< > $@

tutprog_triangle: tutprog_triangle.dats
	$(ATSCC) -o $@ $< `pkg-config gtk+-2.0 --cflags --libs`

clean:: ; $(RMF) tutprog_triangle
clean:: ; $(RMF) tutprog_triangle0
clean:: ; $(RMF) tutprog_triangle1

cleanall:: ; $(RMF) tutprog_triangle.dats
cleanall:: ; $(RMF) tutprog_triangle.dats.extract

######

tutprog_sqrcirc: tutprog_sqrcirc.dats
	$(ATSCC) -o $@ $< `pkg-config cairo --cflags --libs`
tutprog_sqrcirc.png: tutprog_sqrcirc ; ./$<

clean:: ; $(RMF) tutprog_sqrcirc
cleanall:: ; $(RMF) tutprog_sqrcirc.png

######

illucircmot: illucircmot.dats
	$(ATSCC) -o $@ $< `pkg-config cairo --cflags --libs` -lm
illucircmot.png: illucircmot ; ./$<

clean:: ; $(RMF) illucircmot
cleanall:: ; $(RMF) illucircmot.png

######

illuwavy: illuwavy.dats
	$(ATSCC) -o $@ $< `pkg-config gtk+-2.0 --cflags --libs`
illuwavy.png: illuwavy.dats
	$(ATSCC) -DATS ISPNG -o illuwavy $< `pkg-config gtk+-2.0 --cflags --libs` && ./illuwavy

clean:: ; $(RMF) illuwavy
cleanall:: ; $(RMF) illuwavy.png

######

tutprog_showtext: tutprog_showtext.dats
	$(ATSCC) -o $@ tutprog_showtext.dats `pkg-config cairo --cflags --libs`
tutprog_showtext.png: tutprog_showtext; ./$<

clean:: ; $(RMF) tutprog_showtext
cleanall:: ; $(RMF) tutprog_showtext.png

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_atxt.txt
clean:: ; $(RMF) *_atxt.dats
clean:: ; $(RMF) *_dats.c

cleanall:: clean

###### end of [Makefile] ######
