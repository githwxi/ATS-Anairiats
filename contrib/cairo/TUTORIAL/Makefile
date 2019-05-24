#
#
# A Simple Makefile
#
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSDOC=$(ATSHOMEQ)/bin/atsdoc
#LIBATSDOC=$(ATSHOMEQ)/libatsdoc

######

DBSRC= \
  chap_hello_atxt.db \
  chap_objtypes_atxt.db \
  chap_funtypes_atxt.db \
  chap_drawline_atxt.db \
  chap_drawsqrcirc_atxt.db \
  chap_drawtext_atxt.db \

######

all:: html
all:: clean

######

pdf: main.db $(DBSRC) ; jw -b pdf --output PDF/ main.db
html: main.db $(DBSRC) ; jw -b html --output HTML/ main.db

######

chap_hello: chap_hello_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_hello_atxt.dats: chap_hello.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_hello_atxt.txt
chap_hello_atxt.db: chap_hello ; ./chap_hello > $@

clean:: ; $(RMF) chap_hello 
cleanall:: ; $(RMF) chap_hello_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_hello.dats

######

chap_objtypes: chap_objtypes_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_objtypes_atxt.dats: chap_objtypes.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_objtypes_atxt.txt
chap_objtypes_atxt.db: chap_objtypes ; ./chap_objtypes > $@

clean:: ; $(RMF) chap_objtypes 
cleanall:: ; $(RMF) chap_objtypes_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_objtypes.dats

######

chap_funtypes: chap_funtypes_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_funtypes_atxt.dats: chap_funtypes.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_funtypes_atxt.txt
chap_funtypes_atxt.db: chap_funtypes ; ./chap_funtypes > $@

clean:: ; $(RMF) chap_funtypes 
cleanall:: ; $(RMF) chap_funtypes_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_funtypes.dats

######

chap_drawline: chap_drawline_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_drawline_atxt.dats: chap_drawline.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_drawline_atxt.txt
chap_drawline_atxt.db: chap_drawline ; ./chap_drawline > $@

clean:: ; $(RMF) chap_drawline 
cleanall:: ; $(RMF) chap_drawline_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_drawline.dats

######

chap_drawsqrcirc: chap_drawsqrcirc_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_drawsqrcirc_atxt.dats: chap_drawsqrcirc.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_drawsqrcirc_atxt.txt
chap_drawsqrcirc_atxt.db: chap_drawsqrcirc ; ./chap_drawsqrcirc > $@

clean:: ; $(RMF) chap_drawsqrcirc 
cleanall:: ; $(RMF) chap_drawsqrcirc_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_drawsqrcirc.dats

######

chap_drawtext: chap_drawtext_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_drawtext_atxt.dats: chap_drawtext.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_drawtext_atxt.txt
chap_drawtext_atxt.db: chap_drawtext ; ./chap_drawtext > $@

clean:: ; $(RMF) chap_drawtext 
cleanall:: ; $(RMF) chap_drawtext_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_drawtext.dats

######

upload:: upload_pdf
upload_pdf: pdf; scp -r PDF/*.pdf \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/DOCUMENT/ATSCAIRO/PDF

upload:: upload_html
upload_html: html; scp -r HTML/*.html \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/DOCUMENT/ATSCAIRO/HTML

upload_code: ; scp -r CODE/*.dats \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/DOCUMENT/ATSCAIRO/CODE
upload_image: ; scp -r CODE/*.png \
  ats-hwxi,ats-lang@web.sourceforge.net:htdocs/DOCUMENT/ATSCAIRO/IMAGE

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c *_?ats.o

cleanall:: clean
cleanall:: ; $(RMF) HTML/*.html

###### end of [Makefile] ######
