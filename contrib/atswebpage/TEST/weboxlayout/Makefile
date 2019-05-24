#
# A simple Makefile
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt
ATSDOC=$(ATSHOME)/bin/atsdoc

######

ATSWEBPAGE=$(ATSHOME)/contrib/atswebpage/atsctrb_atswebpage.o

######

all:: template.html

######

template: \
  template_atxt.dats ; $(ATSCC) -o $@ $< $(ATSWEBPAGE) -latsdoc
template_atxt.dats: params.hats layout.dats \
  template.atxt ; $(ATSDOC) -do $@ -i template.atxt > template_atxt.txt
template.html: template ; ./$< > $@
cleanall:: ; $(RMF) template
cleanall:: ; $(RMF) template.html
cleanall:: ; $(RMF) template_atxt.dats
cleanall:: ; $(RMF) template_atxt.txt

######

RMF=rm -f

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o *_?ats.c

cleanall:: clean
cleanall:: ; $(RMF) styles/*.css

###### end of [Makefile] ######
