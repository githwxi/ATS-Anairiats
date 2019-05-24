#
#
# A simple Makefile for documenting the grammar of ATS
#
#

######

ATSGRAMMAR=$(ATSHOME)/utils/atsgrammar/atsgrammar

######

all:: ats_grammar_desc.html
ats_grammar_desc.html: ; $(ATSGRAMMAR) --format=desc_html > $@

all:: ats_grammar_yats.html
ats_grammar_yats.html: ; $(ATSGRAMMAR) --format=yats_html > $@

######

RMF = rm -f

######

clean::
	$(RMF) *~

cleanall:: clean
	$(RMF) ats_grammar_desc.html
	$(RMF) ats_grammar_yats.html

###### end of [Makefile] ######
