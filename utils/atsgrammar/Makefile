#
#
# A simple Makefile for documenting the grammar of ATS
#
#

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

ATSGCFLAG=-D_ATS_GCATS

######

OBJECT := \
  atsgrammar_sats.o \
  atsgrammar_tyname_dats.o \
  atsgrammar_symbol_dats.o \
  atsgrammar_grmrule_dats.o \
  atsgrammar_global_dats.o \
  atsgrammar_emit_yats_dats.o \
  atsgrammar_emit_yats_html_dats.o \
  atsgrammar_emit_desc_dats.o \
  atsgrammar_emit_desc_html_dats.o \
  atsgrammar_main_dats.o \

######

atsgrammar: $(OBJECT); $(ATSCC) $(ATSGCFLAG) -o $@ $(OBJECT)

######

atsgrammar_sats.o: atsgrammar.sats
	$(ATSCC) -c -o $@ $<

atsgrammar_tyname_dats.o: atsgrammar_tyname.dats
	$(ATSCC) -c -o $@ $<

atsgrammar_symbol_dats.o: atsgrammar_symbol.dats
	$(ATSCC) -c -o $@ $<

atsgrammar_grmrule_dats.o: atsgrammar_grmrule.dats
	$(ATSCC) -c -o $@ $<

atsgrammar_global_dats.o: atsgrammar_global.dats
	$(ATSCC) -c -o $@ $<

atsgrammar_emit_yats_dats.o: atsgrammar_emit_yats.dats
	$(ATSCC) -c -o $@ $<
atsgrammar_emit_yats_html_dats.o: atsgrammar_emit_yats_html.dats
	$(ATSCC) -c -o $@ $<

atsgrammar_emit_desc_dats.o: atsgrammar_emit_desc.dats
	$(ATSCC) -c -o $@ $<
atsgrammar_emit_desc_html_dats.o: atsgrammar_emit_desc_html.dats
	$(ATSCC) -c -o $@ $<

atsgrammar_main_dats.o: atsgrammar_main.dats
	$(ATSCC) -c -o $@ $<

######

ats_grammar.yats: atsgrammar; ./atsgrammar --format=yats > $@
ats_grammar_yats.html: atsgrammar; ./atsgrammar --format=yats_html > $@

ats_grammar.desc: atsgrammar; ./atsgrammar --format=desc > $@
ats_grammar_desc.html: atsgrammar; ./atsgrammar --format=desc_html > $@

######

#
# HX: '-o .depend' means appending instead of overwriting
#
depend::
	$(RMF) .depend
	$(ATSOPT) -o .depend -dep1 -s atsgrammar.sats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_tyname.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_symbol.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_grmrule.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_global.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_emit_yats.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_emit_yats_html.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_emit_desc.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_emit_desc_html.dats
	$(ATSOPT) -o .depend -dep1 -d atsgrammar_main.dats
include .depend

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) atsgrammar
	$(RMF) ats_grammar.yats
	$(RMF) ats_grammar.desc

###### end of [Makefile] ######
