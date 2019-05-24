#########################################################################
##                                                                     ##
##                         Applied Type System                         ##
##                                                                     ##
##                              Hongwei Xi                             ##
##                                                                     ##
#########################################################################

##
## ATS/Anairiats - Unleashing the Power of Types!
##
## Copyright (C) 2002-2008 Hongwei Xi, Boston University
##
## All rights reserved
##
## ATS is  free software;  you can redistribute it and/or modify it under
## the  terms of the  GNU General Public License as published by the Free
## Software Foundation; either version 2.1, or (at your option) any later
## version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

## ###### ###### ##
##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: July 2007
##
## ###### ###### ##

#
# HX-2010-04-07:
# this Makefile can support parallel execution: make -j8 (for 8 cores)
#

######

MAKE=make
#MAKE=gmake

CC=gcc

######

YACC=
YACCFLAGS=
ATSYACCFLAGS=

#YACC=yacc # HX: this one should work
#YACCFLAGS=-d -v
#ATSYACCFLAGS=-O2

YACC=byacc # HX: this is the original one
YACCFLAGS=-d -v
ATSYACCFLAGS=-O2

#YACC=bison # HX: this is the default one
#YACCFLAGS=-d -v
#ATSYACCFLAGS=-D_ATS_YYVALISLOCAL -O2

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

ATSCCFLAGS=-g
#ATSCCFLAGS=-O0
#ATSCCFLAGS=-O1
#ATSCCFLAGS=-O2
ATSCCFLAGS=-D_ATS_MULTITHREAD -O2 -g
ATSCCFLAGS=-O2 -g
#ATSCCFLAGS=-O2 -g -DATS_SYNDEFATS

######
#
GCFLAGS=
#GCFLAGS=-D_ATS_gc
#GCFLAGS=-D_ATS_gcats
#GCFLAGS=-D_ATS_GC
GCFLAGS=-D_ATS_GCATS
GC_o=gc_o
#
#GCFLAGS=-D_ATS_GCATS -pthread
#GC_o=gc_mt_o
#
######

ATSLEX=$(ATSHOME)/bin/atslex

######
#
# HX: The following files are only needed for BOOTSTRAPPING:
#
# prelude_dats_basics.dats
#
# prelude_dats_bool.dats
# prelude_dats_char.dats
#
# prelude_dats_integer.dats
#
# prelude_dats_array.dats
#
# prelude_dats_string.dats
#
# prelude_dats_printf.dats
# prelude_dats_filebas.dats
#
######

SOURCES := \
  ats_array.sats ats_array.dats \
  ats_charlst.sats ats_charlst.dats \
  ats_comarg.sats ats_comarg.dats \
  ats_counter.sats ats_counter.dats \
  ats_debug.sats ats_debug.dats \
  ats_effect.sats ats_effect.dats \
  ats_error.sats ats_error.dats \
  ats_filename.sats ats_filename.dats \
  ats_fixity.sats ats_fixity_prec.dats ats_fixity_fxty.dats \
  ats_global.sats ats_global.dats \
  ats_hashtbl.sats ats_hashtbl.dats \
  ats_intinf.sats ats_intinf.dats \
  ats_keyword.sats ats_keyword.dats \
  ats_label.sats ats_label.dats \
  ats_location.sats ats_location.dats \
  ats_namespace.sats ats_namespace.dats \
  ats_posmark.sats ats_posmark.dats \
  ats_stamp.sats ats_stamp.dats \
  ats_symbol.sats ats_symbol.dats \
  ats_symenv.sats ats_symenv.dats \
  ats_symtbl.sats ats_symtbl.dats \
  ats_list.sats ats_list.dats \
  ats_map_lin.sats ats_map_lin.dats \
  ats_reference.sats ats_reference.dats \
  ats_set_fun.sats ats_set_fun.dats \
  ats_parser.sats ats_parser.dats \
  ats_syntax.sats ats_syntax.dats \
  ats_syntax_depgen.dats \
  ats_syntax_taggen.dats \
  ats_syntax_posmark.dats \
  ats_staexp1.sats ats_staexp1.dats \
  ats_staexp1_print.dats \
  ats_dynexp1.sats ats_dynexp1.dats \
  ats_dynexp1_print.dats \
  ats_dynexp1_syndef.sats \
  ats_dynexp1_syndef.dats \
  ats_trans1_env.sats ats_trans1_env.dats \
  ats_e1xp_eval.sats ats_e1xp_eval.dats \
  ats_trans1.sats ats_trans1_sta.dats ats_trans1_dyn.dats \
  ats_staexp2.sats ats_staexp2.dats \
  ats_staexp2_print.dats \
  ats_staexp2_scst.dats \
  ats_staexp2_svVar.dats \
  ats_staexp2_dcon.dats \
  ats_staexp2_util1.dats ats_staexp2_util2.dats \
  ats_staexp2_pprint.sats ats_staexp2_pprint.dats \
  ats_dynexp2.sats ats_dynexp2.dats \
  ats_dynexp2_dcst.dats \
  ats_dynexp2_dmac.dats \
  ats_dynexp2_dvar.dats \
  ats_dynexp2_print.dats \
  ats_dynexp2_util.dats \
  ats_trans2_env.sats ats_trans2_env.dats \
  ats_stadyncst2.sats ats_stadyncst2.dats \
  ats_trans2.sats \
  ats_trans2_sta.dats \
  ats_trans2_dyn1.dats ats_trans2_dyn2.dats \
  ats_macro2.sats ats_macro2.dats \
  ats_patcst2.sats ats_patcst2.dats \
  ats_string_parse.sats ats_string_parse.dats \
  ats_printf_c.lats \
  ats_dynexp3.sats ats_dynexp3.dats \
  ats_dynexp3_print.dats \
  ats_trans3_env.sats \
  ats_trans3_env.dats \
  ats_trans3_env_eff.dats \
  ats_trans3_env_loop.dats \
  ats_trans3_env_met.dats \
  ats_trans3_env_scst.dats \
  ats_trans3_env_state.dats \
  ats_trans3_env_print.dats \
  ats_staexp2_solve.sats ats_staexp2_solve.dats \
  ats_trans3.sats ats_trans3_pat.dats \
  ats_trans3_assgn.dats \
  ats_trans3_deref.dats \
  ats_trans3_view.dats \
  ats_trans3_util.dats \
  ats_trans3_exp_up.dats \
  ats_trans3_exp_dn.dats \
  ats_trans3_loop.dats ats_trans3_dec.dats \
  ats_constraint.sats ats_constraint.dats \
  ats_constraint_print.dats \
  ats_solver_fm.sats ats_solver_fm.dats \
  ats_hiexp.sats ats_hiexp.dats \
  ats_hiexp_print.dats ats_hiexp_util.dats \
  ats_trans4.sats ats_trans4.dats \
  ats_ccomp.sats ats_ccomp.dats \
  ats_ccomp_env.sats ats_ccomp_env.dats \
  ats_ccomp_print.dats \
  ats_ccomp_util.dats \
  ats_ccomp_trans.dats \
  ats_ccomp_trans_clau.dats \
  ats_ccomp_trans_tailcal.dats \
  ats_ccomp_trans_temp.dats \
  ats_ccomp_emit.dats \
  ats_ccomp_main.dats \

SOURCESsta := $(filter %.sats, $(SOURCES))
SOURCESdyn := $(filter %.dats, $(SOURCES))

OBJECTS := $(SOURCES)
OBJECTS := $(patsubst %.sats, %_sats.o, $(OBJECTS))
OBJECTS := $(patsubst %.lats, %_lats_dats.o, $(OBJECTS))
OBJECTS := $(patsubst %.dats, %_dats.o, $(OBJECTS))

######

#LIBOBJS :=
LIBOBJS := -lgmp
LIBATSYNDEF :=
#LIBATSYNDEF := -ldl -latsyndef

######

atsopt: \
  ats_main_dats.o \
  ats_lexer_sats.o ats_lexer_lats_dats.o \
  ats_grammar_yats.o \
  libc_sats.o libats_lex.o \
  $(OBJECTS) ; \
  $(ATSCC) $(GCFLAGS) $(ATSCCFLAGS) -o atsopt $^ $(LIBATSYNDEF) $(LIBOBJS)

######

ats_main_dats.o: \
  ats_main.dats ats_lexer_lats.dats ats_printf_c_lats.dats

######

ats_lexer_lats_dats.o: ats_grammar_yats.h ats_lexer_lats.dats

######

ats_grammar_yats.h: ats_grammar_yats.c
ats_grammar_yats.c: ats_grammar.yats
	$(YACC) $(YACCFLAGS) -o ats_grammar_yats.c ats_grammar.yats
ats_grammar_yats.o: ats_grammar_yats.c
	$(ATSCC) $(ATSYACCFLAGS) -DYYDEBUG=1 -c ats_grammar_yats.c 

######

libc_sats.o: libc_sats_gmp_sats.o libc_sats_time_sats.o ; ld -r -o $@ $^

######

libats_lex.o: \
  libats_lex_lexing_sats.o \
  libats_lex_lexing_dats.o \
  libats_lex_tables_dats.o ; ld -r -o $@ $^

######

%_lats.dats: %.lats ; $(ATSLEX) < $< > $@

######

%_sats.c: %.sats ; $(ATSCC) $(ATSCCFLAGS) -c $<
%_sats.o: %_sats.c ; $(ATSCC) $(ATSCCFLAGS) -c $<

%_dats.c: %.dats ; $(ATSCC) $(ATSCCFLAGS) -c $<
%_dats.o: %_dats.c ; $(ATSCC) $(ATSCCFLAGS) -c $<

######

gc_o:
	cd $(ATSHOME)/ccomp/runtime/GCATS; $(MAKE) gc.o; $(MAKE) clean

gc_mt_o:
	cd $(ATSHOME)/ccomp/runtime/GCATS; $(MAKE) gc_mt.o; $(MAKE) clean

######

XREFOBJ := \
  libats_lex_lexing.dats \
  libats_lex_tables.dats \
  libats_lex_lexing.sats \
  libc_sats_gmp.sats \
  libc_sats_time.sats \
  libc_dats_unistd.dats \

XREFOBJ += $(SOURCES)

XREFOBJ := $(patsubst %.sats, %_sats.html, $(XREFOBJ))
XREFOBJ := $(patsubst %.dats, %_dats.html, $(XREFOBJ))

xref:: $(XREFOBJ)
	$(ATSOPT) --posmark_xref=XREF -d $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null

%_sats.html: %.sats
	$(ATSOPT) --posmark_xref=XREF -s $< > $@

%_dats.html: %.dats
	$(ATSOPT) --posmark_xref=XREF -d $< > $@

######

srclines:
	wc -l \
  ats_main.dats \
  ats_lexer.lats \
  ats_grammar.yats \
  libats_lex_lexing.sats \
  libats_lex_lexing.dats \
  libats_lex_tables.dats \
  ats_main.cats \
  ats_counter.cats \
  ats_gmp.cats \
  ats_intinf.cats \
  ats_solver_fm.cats \
  $(SOURCES)

######

DIR=.

######

RMF=rm -f

######

clean:: ; $(RMF) $(DIR)/*~
clean:: ; $(RMF) $(DIR)/*_?ats.o
clean:: ; $(RMF) $(DIR)/*_?ats.c
clean:: ; $(RMF) $(DIR)/*_?ats.html
clean:: ; $(RMF) $(DIR)/*_lats.dats
clean:: ; $(RMF) $(DIR)/libats_lex.o
clean:: ; $(RMF) $(DIR)/ats_grammar_yats.output

cleanall:: clean
cleanall:: ; $(RMF) ats_grammar_yats.c
cleanall:: ; $(RMF) ats_grammar_yats.h
cleanall:: ; $(RMF) atsopt

######

#
# HX: '--output-a .depend' means appending (instead of writing)
#
depend::
	$(RMF) .depend
	$(ATSOPT) --output-a .depend --depgen -d ats_main.dats
	$(ATSOPT) --output-a .depend --depgen -s $(SOURCESsta) -d $(SOURCESdyn)
-include .depend

######

## end of [Makefile] ##

######
