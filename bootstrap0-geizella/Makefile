#########################################################################
#                                                                       #
#                         Applied Type System                           #
#                                                                       #
#                              Hongwei Xi                               #
#                                                                       #
#########################################################################

#
#  ATS - Unleashing the Power of Types!
#
#  Copyright (C) 2002-2007 Hongwei Xi.
#
#  ATS is free software;  you can  redistribute it and/or modify it under
#  the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
#  Free Software Foundation; either version 2.1, or (at your option)  any
#  later version.
# 
#  ATS is distributed in the hope that it will be useful, but WITHOUT ANY
#  WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
#  FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
#  for more details.
# 
#  You  should  have  received  a  copy of the GNU General Public License
#  along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
#  Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
#  02110-1301, USA.
#

#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex

######

INCLUDES=
OCAMLFLAGS= nums.cma unix.cma
OCAMLOPTFLAGS= -ccopt -O3 nums.cmxa unix.cmxa

######

SOURCES := \
  ats_misc.ml \
  ats_keywords.ml \
  ats_symbol.ml \
  ats_counter.ml \
  ats_label.ml \
  ats_symenv.ml \
  ats_filename.ml \
  ats_location.ml \
  ats_error.ml \
  ats_fixity.ml \
  ats_syntax.ml \
  ats_effect.ml \
  ats_grammar.mly \
  ats_lexer.mll \
  ats_printf_c.mll \
  ats_printf_ats.mll \
  ats_parser.ml \
  ats_string_parser.ml \
  ats_staexp1.ml \
  ats_env1.ml \
  ats_dynexp1.ml \
  ats_errmsg1.ml \
  ats_trans1.ml \
  ats_staexp2.ml \
  ats_staenv2.ml \
  ats_stacst2.ml \
  ats_svar_stamp.ml \
  ats_svar_bind.ml \
  ats_staexp2_util.ml \
  ats_dynexp2.ml \
  ats_dynexp2_util.ml \
  ats_stadynenv2.ml \
  ats_name_space.ml \
  ats_dyncst2.ml \
  ats_errmsg2.ml \
  ats_trans2.ml \
  ats_macro.ml \
  ats_metric.ml \
  ats_patcst2.ml \
  ats_dynexp3.ml \
  ats_errmsg3.ml \
  ats_staenv3.ml \
  ats_solver_fm.ml \
  ats_constraint.ml \
  ats_staexp2_solve.ml \
  ats_dynenv3.ml \
  ats_trans3_pat.ml \
  ats_trans3.ml \
  ats_hiexp.ml \
  ats_hiexp_util.ml \
  ats_trans4.ml \
  ats_ccomp.ml \
  ats_ccomp_util.ml \
  ats_ccomp_trans.ml \
  ats_ccomp_cprint.ml \
  ats_ccomp_main.ml \
  ats_arg.ml \
  ats_main_cc.ml \

######

MLS := $(filter %.ml, $(SOURCES))
MLYS := $(filter %.mly, $(SOURCES))
MLLS := $(filter %.mll, $(SOURCES))

SRCS := $(patsubst %.mll, %.ml, $(patsubst %.mly, %.ml, $(SOURCES)))
OBJS := $(SRCS:.ml=.cmo)
OPTOBJS := $(OBJS:.cmo=.cmx)

######

CAT=cat
RMF=rm -f
WCL=wc -l

######

.PHONY: all

######

all:: depend
all:: atsopt

######

atsopt: $(OPTOBJS) ats_simplex.o ats_omega.o
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o atsopt ats_simplex.o ats_omega.o $(OPTOBJS) -cclib -lgmp

######

ats_lexer.ml: ats_lexer.mll
	$(OCAMLLEX) ats_lexer.mll

ats_grammar.ml \
ats_grammar.mli: \
ats_syntax.ml ats_grammar.mly
	$(OCAMLYACC) -v ats_grammar.mly

ats_printf_c.ml: ats_printf_c.mll
	$(OCAMLLEX) ats_printf_c.mll

ats_printf_ats.ml: ats_printf_ats.mll
	$(OCAMLLEX) ats_printf_ats.mll

######
#
clean:: ; $(RMF) ats_grammar.output
clean:: ; $(RMF) *.cm[iox] *.o *.cma *.cmxa *~
#
# clean:: ; $(RMF) ats_lexer.ml ats_grammar.ml ats_grammar.mli
#
######

cleanall:: clean
cleanall:: ; $(RMF) atsopt

######

srclines:: ; \
$(WCL) \
  ats_misc.ml \
  ats_keywords.ml \
  ats_keywords.mli \
  ats_symbol.ml \
  ats_symbol.mli \
  ats_counter.ml \
  ats_counter.mli \
  ats_label.ml \
  ats_label.mli \
  ats_symenv.ml \
  ats_symenv.mli \
  ats_filename.ml \
  ats_filename.mli \
  ats_location.ml \
  ats_error.ml \
  ats_error.mli \
  ats_fixity.ml \
  ats_fixity.mli \
  ats_syntax.ml \
  ats_effect.ml \
  ats_grammar.mly \
  ats_lexer.mll \
  ats_printf_c.mll \
  ats_printf_ats.mll \
  ats_parser.ml \
  ats_parser.mli \
  ats_string_parser.ml \
  ats_staexp1.ml \
  ats_env1.ml \
  ats_env1.mli \
  ats_dynexp1.ml \
  ats_errmsg1.ml \
  ats_trans1.ml \
  ats_staexp2.ml \
  ats_staenv2.ml \
  ats_staenv2.mli \
  ats_stacst2.ml \
  ats_svar_stamp.ml \
  ats_svar_bind.ml \
  ats_staexp2_util.ml \
  ats_dynexp2.ml \
  ats_dynexp2_util.ml \
  ats_stadynenv2.ml \
  ats_stadynenv2.mli \
  ats_name_space.ml \
  ats_dyncst2.ml \
  ats_errmsg2.ml \
  ats_trans2.ml \
  ats_trans2.mli \
  ats_macro.ml \
  ats_metric.ml \
  ats_patcst2.ml \
  ats_patcst2.mli \
  ats_dynexp3.ml \
  ats_errmsg3.ml \
  ats_staenv3.ml \
  ats_solver_fm.ml \
  ats_constraint.ml \
  ats_staexp2_solve.ml \
  ats_staexp2_solve.mli \
  ats_dynenv3.ml \
  ats_trans3_pat.ml \
  ats_trans3.ml \
  ats_hiexp.ml \
  ats_hiexp_util.ml \
  ats_trans4.ml \
  ats_ccomp.ml \
  ats_ccomp_util.ml \
  ats_ccomp_trans.ml \
  ats_ccomp_cprint.ml \
  ats_ccomp_main.ml \
  ats_arg.ml \
  ats_main_cc.ml \

######

allsrc:: ; $(CAT) $(SOURCES) > ats_geizella_allsrc.txt

######

#common rules:

.SUFFIXES: .ml .mli .cmi .cmo .cmx

.ml.cmo:
	$(OCAMLC) $(INCLUDES) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(INCLUDES) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(INCLUDES) $(OCAMLOPTFLAGS) -c $<

.c.o:
	$(OCAMLOPT) $(INCLUDES) -c -ccopt -std=c99 -ccopt -O3 -ccopt -funroll-loops $<

######

depend::
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

######

-include .depend

###### end of [Makefile] ######
