######
#
# A simple Makefile
#
######

ATSCC=$(ATSHOME)/bin/atscc
ATSDOC=$(ATSHOME)/bin/atsdoc

######

all:: HOME
all:: DOWNLOAD
all:: DOCUMENT
all:: LIBRARY
all:: RESOURCE
all:: COMMUNITY
all:: EXAMPLE
all:: IMPLEMENT
all:: PAPER
#all:: clean

######

OATSYNTAX=$(ATSHOME)/utils/atsyntax/atsyntax.o
OATSWEBPAGE=$(ATSHOME)/contrib/atswebpage/atsctrb_atswebpage.o

######

atslangweb_layout.dats: atslangweb_params.hats ; touch $@

atslangweb_temp: \
  atslangweb_temp_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_temp_atxt.dats: atslangweb_layout.dats \
  atslangweb_temp.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_temp.atxt > atslangweb_temp_atxt.txt
atslangweb_temp.html: atslangweb_temp ; ./$< > $@

clean:: ; $(RMF) atslangweb_temp
cleanall:: ; $(RMF) atslangweb_temp.html
cleanall:: ; $(RMF) styles/atslangweb_temp.css

######

XRFLAGS=`pkg-config cairo --cflags --libs`

atslangweb_bgimages: \
  atslangweb_bgimages.dats; $(ATSCC) -o $@ $< $(XRFLAGS) -lm
clean:: ; $(RMF) atslangweb_bgimages

BGIMAGES: atslangweb_bgimages ; ./$<
cleanall:: ; $(RMF) images/theSidebar_bgimage.png
cleanall:: ; $(RMF) images/thePageBody_bgimage.png

######

atslangweb_home: \
  atslangweb_home_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_home_atxt.dats: \
  atslangweb_home.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_home.atxt > atslangweb_home_atxt.txt
HOME: atslangweb_home atslangweb_temp.html ; ./$< > atslangweb_home.html

clean:: ; $(RMF) atslangweb_home
cleanall:: ; $(RMF) atslangweb_home.html
cleanall:: ; $(RMF) styles/atslangweb_home.css

######

atslangweb_download: \
  atslangweb_download_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_download_atxt.dats: \
  atslangweb_download.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_download.atxt > atslangweb_download_atxt.txt
DOWNLOAD:: atslangweb_download atslangweb_temp.html ; ./$< > $@/atslangweb_download.html

clean:: ; $(RMF) atslangweb_download
cleanall:: ; $(RMF) DOWNLOAD/atslangweb_download.html
cleanall:: ; $(RMF) styles/atslangweb_download.css

######

atslangweb_document: \
  atslangweb_document_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_document_atxt.dats: \
  atslangweb_document.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_document.atxt > atslangweb_document_atxt.txt
DOCUMENT:: atslangweb_document atslangweb_temp.html ; ./$< > $@/atslangweb_document.html

clean:: ; $(RMF) atslangweb_document
cleanall:: ; $(RMF) DOCUMENT/atslangweb_document.html
cleanall:: ; $(RMF) styles/atslangweb_document.css

######

atslangweb_library: \
  atslangweb_library_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_library_atxt.dats: \
  atslangweb_library.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_library.atxt > atslangweb_library_atxt.txt
LIBRARY:: atslangweb_library atslangweb_temp.html ; ./$< > $@/atslangweb_library.html

clean:: ; $(RMF) atslangweb_library
cleanall:: ; $(RMF) LIBRARY/atslangweb_library.html
cleanall:: ; $(RMF) styles/atslangweb_library.css

######

atslangweb_resource: \
  atslangweb_resource_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_resource_atxt.dats: \
  atslangweb_resource.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_resource.atxt > atslangweb_resource_atxt.txt
RESOURCE:: atslangweb_resource atslangweb_temp.html ; ./$< > $@/atslangweb_resource.html

clean:: ; $(RMF) atslangweb_resource
cleanall:: ; $(RMF) RESOURCE/atslangweb_resource.html
cleanall:: ; $(RMF) styles/atslangweb_resource.css

######

atslangweb_community: \
  atslangweb_community_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_community_atxt.dats: \
  atslangweb_community.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_community.atxt > atslangweb_community_atxt.txt
COMMUNITY:: atslangweb_community atslangweb_temp.html ; ./$< > $@/atslangweb_community.html

clean:: ; $(RMF) atslangweb_community
cleanall:: ; $(RMF) COMMUNITY/atslangweb_community.html
cleanall:: ; $(RMF) styles/atslangweb_community.css

######

atslangweb_example: \
  atslangweb_example_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_example_atxt.dats: \
  atslangweb_example.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_example.atxt > atslangweb_example_atxt.txt
EXAMPLE:: atslangweb_example atslangweb_temp.html ; ./$< > $@/atslangweb_example.html

clean:: ; $(RMF) atslangweb_example
cleanall:: ; $(RMF) EXAMPLE/atslangweb_example.html
cleanall:: ; $(RMF) styles/atslangweb_example.css

######

atslangweb_implement: \
  atslangweb_implement_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_implement_atxt.dats: \
  atslangweb_implement.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_implement.atxt > atslangweb_implement_atxt.txt
IMPLEMENT:: atslangweb_implement atslangweb_temp.html ; ./$< > $@/atslangweb_implement.html

clean:: ; $(RMF) atslangweb_implement
cleanall:: ; $(RMF) IMPLEMENT/atslangweb_implement.html
cleanall:: ; $(RMF) styles/atslangweb_implement.css

######

atslangweb_paper: \
  atslangweb_paper_atxt.dats ; $(ATSCC) -o $@ $< $(OATSYNTAX) $(OATSWEBPAGE) -latsdoc
atslangweb_paper_atxt.dats: \
  atslangweb_paper.atxt ; $(ATSDOC) --outcode $@ -i atslangweb_paper.atxt > atslangweb_paper_atxt.txt
PAPER:: atslangweb_paper atslangweb_temp.html ; ./$< > $@/atslangweb_paper.html

clean:: ; $(RMF) atslangweb_paper
cleanall:: ; $(RMF) PAPER/atslangweb_paper.html
cleanall:: ; $(RMF) styles/atslangweb_paper.css

######
#
# for creating a shell, please do
#
# ssh -t ats-hwxi,ats-lang@shell.sourceforge.net create
#
######

uploadall::
uploadall:: upload_home
uploadall:: upload_download
uploadall:: upload_document
uploadall:: upload_library
uploadall:: upload_resource
uploadall:: upload_community
uploadall:: upload_example
uploadall:: upload_paper
uploadall:: upload_implement
uploadall:: upload_styles
uploadall:: upload_images

upload_home:: ; scp atslangweb_home.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/

upload_download:: ; scp DOWNLOAD/atslangweb_download.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOWNLOAD

upload_document:: ; scp DOCUMENT/atslangweb_document.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/DOCUMENT

upload_library:: ; scp LIBRARY/atslangweb_library.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/LIBRARY

upload_resource:: ; scp RESOURCE/atslangweb_resource.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/RESOURCE

upload_community:: ; scp COMMUNITY/atslangweb_community.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/COMMUNITY

upload_example:: ; scp EXAMPLE/atslangweb_example.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/EXAMPLE

upload_implement:: ; scp IMPLEMENT/atslangweb_implement.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/IMPLEMENT

upload_paper:: ; scp PAPER/atslangweb_paper.html \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/PAPER

upload_styles: ; scp -r styles/*.css \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/styles
upload_images: ; scp -r images/*.ico images/*.png \
  ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/images

#####################################################################
# upload_html: ; scp \						    #
#   atslangweb_home.html \					    #
#   DOWNLOAD/atslangweb_download.html \				    #
#   DOCUMENT/atslangweb_document.html \				    #
#   LIBRARY/atslangweb_library.html \				    #
#   RESOURCE/atslangweb_resource.html \				    #
#   COMMUNITY/atslangweb_community.html \                           #
#   EXAMPLE/atslangweb_example.html \				    #
#   IMPLEMENT/atslangweb_implement.html \			    #
#   PAPER/atslangweb_paper.html \				    #
#   ats-hwxi@web.sourceforge.net:/home/groups/a/at/ats-lang/htdocs/ #
#####################################################################

######

CPF=cp -f
RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o *_?ats.c
clean:: ; $(RMF) *_atxt.txt
clean:: ; $(RMF) *_atxt.dats

cleanall:: clean

######
