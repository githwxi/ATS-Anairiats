##
## Course: Concepts of Programming Languages (BU CAS CS 320)
## Semester: Summer I, 2009
## Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
##

##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: June, 2009
##

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

CCFLAGS=
CCFLAGS=-O2
GCFLAG=
GCFLAG=-D_ATS_GCATS

######

LIBPARCOMB=$(ATSHOME)/contrib/parcomb/atsctrb_parcomb.o

######

SOURCES=\
  stfpl_main.dats \
  error.sats error.dats \
  symbol.sats symbol.dats \
  absyn.sats absyn.dats \
  fixity.sats fixity.dats \
  parser.sats parser.dats \
  interp0.sats interp0.dats \
  trans1.sats trans1.dats \
  interp1.sats interp1.dats \

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))

######

stfpl: $(OBJECTS)
	$(ATSCC) $(CCFLAGS) $(GCFLAG) -o stfpl $(OBJECTS) $(LIBPARCOMB)

######

test:: stfpl
	./stfpl < TEST/f91.stfpl
	./stfpl < TEST/fact.stfpl
	./stfpl < TEST/fact_fix.stfpl
	./stfpl < TEST/fib.stfpl
	./stfpl < TEST/evenodd.stfpl
	./stfpl < TEST/twice.stfpl
	./stfpl < TEST/coin.stfpl
	./stfpl < TEST/bsearch_fun.stfpl
	./stfpl < TEST/queens.stfpl

######

%_sats.o: %.sats
	$(ATSCC) $(CCFLAGS) -o $@ -c $< || touch $@

%_dats.o: %.dats
	$(ATSCC) $(CCFLAGS) -o $@ -c $< || touch $@

######

xref::
	$(ATSOPT) --posmark_xref=XREF \
          -d $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
	$(ATSOPT) --posmark_xref=XREF \
          -d stfpl_main.dats > stfpl_main_dats.html
	$(ATSOPT) --posmark_xref=XREF -d error.dats > error_dats.html
	$(ATSOPT) --posmark_xref=XREF -d symbol.dats > symbol_dats.html
	$(ATSOPT) --posmark_xref=XREF -d absyn.dats > absyn_dats.html
	$(ATSOPT) --posmark_xref=XREF -d parser.dats > parser_dats.html
	$(ATSOPT) --posmark_xref=XREF -d trans1.dats > trans1_dats.html
	$(ATSOPT) --posmark_xref=XREF -s interp1.sats > interp1_sats.html
	$(ATSOPT) --posmark_xref=XREF -d interp1.dats > interp1_dats.html

######

chmod::
	chmod 644 Makefile
	chmod 644 *.?ats
	chmod 644 *_?ats.html
	cd XREF; chmod 644 *.html

######

#
#svn propdel svn:externals .
#svn propset svn:externals . --file [a_file_containing_the_following_line]
#PARCOMB https://ats-lang.svn.sourceforge.net/svnroot/ats-lang/contrib/parcomb
#

######

RMF=rm -f

######

SOURCESsta := $(filter %.sats, $(SOURCES))
SOURCESdyn := $(filter %.dats, $(SOURCES))

depend::
	$(RMF) .depend
	$(ATSOPT) -o .depend -dep1 -s $(SOURCESsta) -d $(SOURCESdyn)
include .depend

######

clean::
	$(RMF) *~
	$(RMF) *_sats.c *_dats.c
	$(RMF) *_sats.o *_dats.o

cleanall: clean
	$(RMF) stfpl
	$(RMF) *_?ats.html */*_?ats.html
	$(RMF) XREF/*.html

distclean:: cleanall

######

lines::
	wc -l *.?ats

###### end of [Makefile] ######
