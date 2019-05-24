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

all:: html
all:: clean

######

typecheck::

######

cleanall::

######

DBSRC := \
  main.db \
  preface.db \
  chap_syncolor_atxt.db \
  chap_filename_atxt.db \
  chap_fileincl_atxt.db \
  chap_fixity_atxt.db \
  chap_mainats_atxt.db \
  chap_tailrec_atxt.db \
  chap_mutailrec_atxt.db \
  chap_termetric_atxt.db \
  chap_hofun_atxt.db \
  chap_polytemp_atxt.db \
  chap_printf_atxt.db \
  chap_funlist_atxt.db \
  chap_array_atxt.db \
  chap_reference_atxt.db \
  chap_callbyref_atxt.db \
  chap_lazyeval_atxt.db \
  chap_castfn_atxt.db \
  chap_stkalloc_atxt.db \

######

html:: $(DBSRC)
	jw -b html --output HTML/ main.db
cleanall:: ; $(RMF) HTML/*.html

pdf: $(DBSRC)
	jw -b pdf --output PDF/ main.db
cleanall:: ; $(RMF) PDF/main.pdf

######

chap_syncolor: chap_syncolor_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_syncolor_atxt.dats: chap_syncolor.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_syncolor_atxt.txt
chap_syncolor_atxt.db: chap_syncolor ; ./$< > $@

cleanall:: ; $(RMF) chap_syncolor
cleanall:: ; $(RMF) chap_syncolor_atxt.*

######

chap_filename: chap_filename_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_filename_atxt.dats: chap_filename.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_filename_atxt.txt
chap_filename_atxt.db: chap_filename ; ./$< > $@

cleanall:: ; $(RMF) chap_filename 
cleanall:: ; $(RMF) chap_filename_atxt.*

######

chap_fileincl: chap_fileincl_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_fileincl_atxt.dats: chap_fileincl.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_fileincl_atxt.txt
chap_fileincl_atxt.db: chap_fileincl ; ./$< > $@

cleanall:: ; $(RMF) chap_fileincl 
cleanall:: ; $(RMF) chap_fileincl_atxt.*

######

chap_fixity: chap_fixity_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_fixity_atxt.dats: chap_fixity.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_fixity_atxt.txt
chap_fixity_atxt.db: chap_fixity ; ./$< > $@

cleanall:: ; $(RMF) chap_fixity
cleanall:: ; $(RMF) chap_fixity_atxt.*

######

chap_mainats: chap_mainats_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_mainats_atxt.dats: chap_mainats.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_mainats_atxt.txt
chap_mainats_atxt.db: chap_mainats ; ./$< > $@

cleanall:: ; $(RMF) chap_mainats
cleanall:: ; $(RMF) chap_mainats_atxt.*

######

chap_tailrec: chap_tailrec_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_tailrec_atxt.dats: chap_tailrec.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_tailrec_atxt.txt
chap_tailrec_atxt.db: chap_tailrec ; ./$< > $@

cleanall:: ; $(RMF) chap_tailrec
cleanall:: ; $(RMF) chap_tailrec_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_tailrec.dats

######

chap_mutailrec: chap_mutailrec_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_mutailrec_atxt.dats: chap_mutailrec.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_mutailrec_atxt.txt
chap_mutailrec_atxt.db: chap_mutailrec ; ./$< > $@

cleanall:: ; $(RMF) chap_mutailrec
cleanall:: ; $(RMF) chap_mutailrec_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_mutailrec.dats

######

chap_termetric: chap_termetric_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_termetric_atxt.dats: chap_termetric.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_termetric_atxt.txt
chap_termetric_atxt.db: chap_termetric ; ./$< > $@

cleanall:: ; $(RMF) chap_termetric
cleanall:: ; $(RMF) chap_termetric_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_termetric.dats

######

chap_hofun: chap_hofun_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_hofun_atxt.dats: chap_hofun.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_hofun_atxt.txt
chap_hofun_atxt.db: chap_hofun ; ./$< > $@

cleanall:: ; $(RMF) chap_hofun
cleanall:: ; $(RMF) chap_hofun_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_hofun.dats

######

chap_polytemp: chap_polytemp_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_polytemp_atxt.dats: chap_polytemp.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_polytemp_atxt.txt
chap_polytemp_atxt.db: chap_polytemp ; ./$< > $@

cleanall:: ; $(RMF) chap_polytemp
cleanall:: ; $(RMF) chap_polytemp_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_polytemp.dats

######

chap_printf: chap_printf_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_printf_atxt.dats: chap_printf.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_printf_atxt.txt
chap_printf_atxt.db: chap_printf ; ./$< > $@

cleanall:: ; $(RMF) chap_printf
cleanall:: ; $(RMF) chap_printf_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_printf.dats

######

chap_funlist: chap_funlist_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_funlist_atxt.dats: chap_funlist.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_funlist_atxt.txt
chap_funlist_atxt.db: chap_funlist ; ./$< > $@

cleanall:: ; $(RMF) chap_funlist
cleanall:: ; $(RMF) chap_funlist_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_funlist.dats

######

chap_array: chap_array_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_array_atxt.dats: chap_array.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_array_atxt.txt
chap_array_atxt.db: chap_array ; ./$< > $@

cleanall:: ; $(RMF) chap_array
cleanall:: ; $(RMF) chap_array_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_array.dats

######

chap_reference: chap_reference_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_reference_atxt.dats: chap_reference.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_reference_atxt.txt
chap_reference_atxt.db: chap_reference ; ./$< > $@

cleanall:: ; $(RMF) chap_reference
cleanall:: ; $(RMF) chap_reference_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_reference.dats

######

chap_callbyref: chap_callbyref_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_callbyref_atxt.dats: chap_callbyref.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_callbyref_atxt.txt
chap_callbyref_atxt.db: chap_callbyref ; ./$< > $@

cleanall:: ; $(RMF) chap_callbyref 
cleanall:: ; $(RMF) chap_callbyref_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_callbyref.dats

######

chap_lazyeval: chap_lazyeval_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_lazyeval_atxt.dats: chap_lazyeval.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_lazyeval_atxt.txt
chap_lazyeval_atxt.db: chap_lazyeval ; ./$< > $@

cleanall:: ; $(RMF) chap_lazyeval 
cleanall:: ; $(RMF) chap_lazyeval_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_lazyeval.dats

######

chap_castfn: chap_castfn_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_castfn_atxt.dats: chap_castfn.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_castfn_atxt.txt
chap_castfn_atxt.db: chap_castfn ; ./chap_castfn > $@

cleanall:: ; $(RMF) chap_castfn 
cleanall:: ; $(RMF) chap_castfn_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_castfn.dats

######

chap_stkalloc: chap_stkalloc_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ $< -latsdoc
chap_stkalloc_atxt.dats: chap_stkalloc.atxt
	$(ATSDOC) --outcode $@ -i $< > chap_stkalloc_atxt.txt
chap_stkalloc_atxt.db: chap_stkalloc ; ./chap_stkalloc > $@

cleanall:: ; $(RMF) chap_stkalloc 
cleanall:: ; $(RMF) chap_stkalloc_atxt.*

typecheck:: ; $(ATSCC) -tc CODE/chap_stkalloc.dats

######

upload:
	scp -r HTML ats-hwxi,ats-lang@web.sourceforge.net:htdocs/DOCUMENT/TUTORIALATS

uploadloc:
	cp -rf HTML $(HOME)/public_html/ATS/DOCUMENT/TUTORIALATS
	chmod 644 $(HOME)/public_html/ATS/DOCUMENT/TUTORIALATS/HTML/*.html

######

upload_pdf:
	scp -r PDF/main.pdf ats-hwxi,ats-lang@web.sourceforge.net:htdocs/DOCUMENT/TUTORIALATS/PDF/

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
cleanall:: ; $(RMF) CODE/chap_*.dats

###### end of [Makefile] ######
