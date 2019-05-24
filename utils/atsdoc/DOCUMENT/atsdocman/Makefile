######
#
# A simple Makefile
#
######

ATSCC=$(ATSHOME)/bin/atscc
ATSDOC=$(ATSHOME)/bin/atsdoc
OATSYNTAX=$(ATSHOME)/utils/atsyntax/atsyntax.o

######

all:: atsdocman.html

######

atsdocman: atsdocman_atxt.dats
	$(ATSCC) -o $@ atsdocman_atxt.dats $(OATSYNTAX) -latsdoc
atsdocman_atxt.dats: atsdocman.atxt
	$(ATSDOC) --outcode $@ -i atsdocman.atxt > atsdocman_atxt.txt
atsdocman.html: atsdocman
	./atsdocman > $@

uploadloc:: atsdocman.html
	$(CPF) $< $(HOME)/public_html/ATS/DOCUMENT/atsdocman.html

upload:: atsdocman.html atsdocman.atxt
	scp -r $^ ats-hwxi,ats-lang@web.sourceforge.net:htdocs/htdocs-old/DOCUMENT/atsdocman/

######

CPF=cp -f
RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o *_?ats.c
clean:: ; $(RMF) *_atxt.txt
clean:: ; $(RMF) *_atxt.dats

cleanall:: clean
cleanall:: ; $(RMF) atsdocman
cleanall:: ; $(RMF) atsdocman.html

######
