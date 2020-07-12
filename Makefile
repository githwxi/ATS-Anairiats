#########################################################################
##                                                                     ##
##                         Applied Type System                         ##
##                                                                     ##
##                              Hongwei Xi                             ##
##                                                                     ##
#########################################################################

##
## ATS/Anairiats - Unleashing the Potential of Types!
##
## Copyright (C) 2002-2010 Hongwei Xi.
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
## along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
## Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
## 02110-1301, USA.
##

######

##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Author: Likai Liu (liulk AT cs DOT bu DOT edu)
## Author: Yuri D'Elia (wavexx AT thregr DOT org)
##

######
#
# Disable parallelism and implicit rules
#
MAKEFLAGS += -j1
#
######
#
all:: config.mk
#
######
#
configure : ; /bin/bash autogen.sh
#
######
#
config.mk : configure ; @echo "Please execute './configure'." ; exit 1 ;
#
######
#
-include config.mk
#
######

DESTDIR :=

export ATSHOME
export ATSHOMERELOC
export ATSHOMEQ

######

ATSHOMEBIN = $(ATSHOMEQ)/bin

######

install:: config.h
#
# recursively install all files in the list except .svn control files.
#
	for d in ccomp/runtime contrib doc libats libc prelude; do \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -d $(DESTDIR)$(ATSNEWHOME)/"$$d" && \
	  find "$$d" -name .svn -prune -o -type f \
            -exec $(INSTALL) -m 644 -D \{} $(DESTDIR)$(ATSNEWHOME)/\{} \; \
	    -print && \
	  find "$$d" -name .svn -prune -o -type l \
            -exec cp -d \{} $(DESTDIR)$(ATSNEWHOME)/\{} \; \
	    -print; \
	done
#
# install specific files in the list as regular files.
#
	for f in \
	    COPYING INSTALL *.txt ccomp/lib/*.a ccomp/lib64/*.a config.h; \
	do \
	  [ -f "$$f" ] || continue; \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -m 644 -D "$$f" $(DESTDIR)$(ATSNEWHOME)/"$$f" && \
	  echo "$$f"; \
	done

	# install specific files in the list as executables.
	for f in bin/*; do \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -m 755 -D "$$f" $(DESTDIR)$(ATSNEWHOME)/"$$f" && \
	  echo "$$f"; \
	done
#
# install multiple copies of wrapper script, for each binary.
#
	for f in bin/*; do \
	  b=`basename "$$f"`; \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -m 755 -D ats_env.sh $(DESTDIR)$(bindir)/"$$b" && \
	  echo install ats_env.sh to $(bindir)/"$$b"; \
	done

######

test:: ; sh test.sh

######

all:: all1

######
#
ATSVER=geizella
ATSVER=anairiats
ATSOPT0=atsopt0-$(ATSVER)
#
######
#
all0:: \
$(ATSOPT0); \
$(CPF) bootstrap0-$(ATSVER)/atsopt bin/atsopt
#
all0:: atsopt1
all0:: bin_atscc
all0:: bin_atslib
all0:: libfiles
all0:: libfiles_mt
all0:: libatsdoca
all0:: bin_atspack
all0:: bin_atslex
all0:: bin_atsdoc_ngc
#
all0:: ; @echo "ATS/Anairiats has been built up successfully!"
all0:: ; @echo "The value of ATSHOME for this build is \"$(ATSHOME)\"."
all0:: ; @echo "The value of ATSHOMERELOC for this build is \"$(ATSHOMERELOC)\"."
#
######
#
all1:: \
$(ATSOPT0); \
$(CPF) bootstrap0-$(ATSVER)/atsopt bin/atsopt
#
all1:: atsopt1
all1:: bin_atscc
all1:: bin_atslib
all1:: libfiles
all1:: libfiles_mt
all1:: libatsdoca
all1:: bin_atspack
#
all1:: GCATS_gc_o
all1:: GCATS_gc_mt_o
#
# atsdoc and atslex may require GC
#
all1:: atsopt1_gc
all1:: bin_atslex
all1:: bin_atsdoc
all1:: atscontrib
#
all1:: ; @echo "ATS/Anairiats has been built up successfully!"
all1:: ; @echo "The value of ATSHOME for this build is \"$(ATSHOME)\"."
all1:: ; @echo "The value of ATSHOMERELOC for this build is \"$(ATSHOMERELOC)\"."
#
######
#
# bootstrapping via ocaml
#
atsopt0-geizella: ; \
make -C bootstrap0-geizella -f ./Makefile atsopt
#
######
#
# bootstrapping via gcc
#
atsopt0-anairiats: ; \
make -C bootstrap0-anairiats -f ./Makefile atsopt
#
######

######
# w/o GC ######
######
#
atsopt1:: ; \
make -C src -f ./Makefile_srcbootstrap all
atsopt1:: ; \
make -C bootstrap1 -f ../Makefile_bootstrap atsopt
#
atsopt1:: ; $(CPF) bootstrap1/atsopt $(ATSHOMEBIN)/atsopt
#
######
# with GC ######
######
#
atsopt1_gc:: ; \
make -C bootstrap1 -f ../Makefile_bootstrap atsopt_gc
#
atsopt1_gc:: ; $(CPF) bootstrap1/atsopt_gc $(ATSHOMEBIN)/atsopt
#
###### contrib libraries ######

atscontrib::
ifeq (1,1)
	make -C contrib/parcomb all
endif
# ifeq ($(HAVE_LIBGLIB20),1)
# 	make -C contrib/glib all
# endif
# ifeq ($(HAVE_LIBGTK20),1)
# 	make -C contrib/cairo all
# 	make -C contrib/pango all
# 	make -C contrib/GTK all
# endif

###### some toplevel commands ######

bin_atscc bin_atslib:
	make -C utils/scripts atscc
	make -C utils/scripts atslib
	$(CPF) utils/scripts/atscc $(ATSHOMEBIN)
	$(CPF) utils/scripts/atslib $(ATSHOMEBIN)
	make -C utils/scripts cleanall

bin_atspack:
	make -C utils/scripts atspack
	$(CPF) utils/scripts/atspack $(ATSHOMEBIN)
	make -C utils/scripts cleanall

bin_atsdoc:
	make -C utils/atsdoc atsdoc
	$(CPF) utils/atsdoc/atsdoc $(ATSHOMEBIN)/atsdoc
	make -C utils/atsdoc cleanall

bin_atsdoc_ngc:
	make -C utils/atsdoc atsdoc_ngc
	$(CPF) utils/atsdoc/atsdoc_ngc $(ATSHOMEBIN)/atsdoc
	make -C utils/atsdoc cleanall

###### library ######
#
ATS_PROOFCHECK=
#
# ATS_PROOFCHECK=-D_ATS_PROOFCHECK # it is deprecated
#
######
#
# $(GCC) -E for preprocessing
#
GCC=gcc
ATSLIB=$(ATSHOMEBIN)/atslib
#
.libfiles_local: .libfiles ; $(GCC) -E -P -x c -o $@ $<
#
libfiles: .libfiles_local
	$(ATSLIB) $(ATS_PROOFCHECK) -O2 --libats
	$(ATSLIB) $(ATS_PROOFCHECK) -O2 --libats_lex
	$(ATSLIB) $(ATS_PROOFCHECK) -O2 --libats_smlbas
#
lib32files: .libfiles_local
	$(ATSLIB) $(ATS_PROOFCHECK) -m32 -O2 --libats
	$(ATSLIB) $(ATS_PROOFCHECK) -m32 -O2 --libats_lex
	$(ATSLIB) $(ATS_PROOFCHECK) -m32 -O2 --libats_smlbas
#
lib64files: .libfiles_local
	$(ATSLIB) $(ATS_PROOFCHECK) -m64 -O2 --libats
	$(ATSLIB) $(ATS_PROOFCHECK) -m64 -O2 --libats_lex
	$(ATSLIB) $(ATS_PROOFCHECK) -m64 -O2 --libats_smlbas
#
######
#
.libfiles_mt_local: .libfiles_mt ; $(GCC) -E -P -x c -o $@ $<
#
libfiles_mt: \
.libfiles_mt_local ; \
$(ATSLIB) $(ATS_PROOFCHECK) -O2 -D_ATS_MULTITHREAD --libats_mt
#
######

libatsdoca: ; make -C libatsdoc

###### a lexer for ATS ######

bin_atslex:: ; make -C utils/atslex atslex
bin_atslex:: ; $(CPF) utils/atslex/atslex $(ATSHOMEBIN)/atslex
bin_atslex:: ; make -C utils/atslex atslex clean

###### GC runtime ######
#
GCATS_gc_o:: ; make -C ccomp/runtime/GCATS gc.o
GCATS_gc_o:: ; make -C ccomp/runtime/GCATS clean
#
GCATS_gc_mt_o:: ; make -C ccomp/runtime/GCATS gc_mt.o
GCATS_gc_mt_o:: ; make -C ccomp/runtime/GCATS clean
#
######
#
package:: ; bin/atspack --source
#
precompiled:: ; bin/atspack --precompiled
precompiled:: ; $(RMRF) usr/share/atshome
precompiled:: ; mv ats-lang-anairiats-* usr/share/atshome
precompiled:: ; \
$(TARZVCF) ats-lang-anairiats-precompiled.tar.gz \
  --exclude=usr/.svn --exclude=usr/bin/.svn --exclude=usr/share/.svn usr/.
#
######
#
srclines:: ; make -C src lines
#
liblines:: ; \
$(WCL) \
prelude/*/*.?ats \
prelude/*/*/*.?ats \
libc/*/*.?ats libc/*/*/*.?ats \
libats/*/*.?ats libats/*/*/*.?ats
#
######
#
CPF=cp -f
RMF=rm -f
RMRF=rm -rf
TARZVCF=tar -zvcf
WCL=wc -l
#
######
#
clean:: ; \
make -C bootstrap0-geizella clean
clean:: ; \
make -C bootstrap0-anairiats clean
#
clean:: ; $(RMF) bootstrap1/*.c
clean:: ; $(RMF) bootstrap1/*.h
clean:: ; $(RMF) bootstrap1/*.cats
clean:: ; $(RMF) bootstrap1/*.o
#
######

cleanall:: clean
cleanall:: ; $(RMF) $(BUILT_CONFIG_FILES)
cleanall:: ; $(RMF) .libfiles_local
cleanall:: ; $(RMF) .libfiles_mt_local
cleanall:: ; $(RMF) src/ats_grammar_yats.c src/ats_grammar_yats.h
cleanall:: ; $(RMF) bin/atsopt
cleanall:: ; $(RMF) bin/atscc bin/atslib bin/atslex bin/atspack
cleanall:: ; $(RMF) bin/atsdoc
cleanall:: ; $(RMF) libatsdoc/libatsdoc.a
cleanall:: ; $(RMF) ccomp/lib/libats.a
cleanall:: ; $(RMF) ccomp/lib/libats_mt.a
cleanall:: ; $(RMF) ccomp/lib/libats_lex.a
cleanall:: ; $(RMF) ccomp/lib/libats_smlbas.a
cleanall:: ; $(RMF) ccomp/lib/output/*
cleanall:: ; $(RMF) ccomp/lib64/libats.a
cleanall:: ; $(RMF) ccomp/lib64/libats_mt.a
cleanall:: ; $(RMF) ccomp/lib64/libats_lex.a
cleanall:: ; $(RMF) ccomp/lib64/libats_smlbas.a
cleanall:: ; $(RMF) ccomp/lib64/output/*
cleanall:: ; $(RMF) contrib/glib/atsctrb_glib.o
cleanall:: ; $(RMF) contrib/cairo/atsctrb_cairo.o
cleanall:: ; $(RMF) contrib/pango/atsctrb_pango.o
cleanall:: ; $(RMF) contrib/X11/atsctrb_X11.o
cleanall:: ; $(RMF) contrib/GTK/atsctrb_GTK.o
cleanall:: ; $(RMF) contrib/GL/atsctrb_GL.o
cleanall:: ; $(RMF) contrib/GL/atsctrb_glut.o
cleanall:: ; $(RMF) contrib/gtkglext/atsctrb_gtkglext.o
cleanall:: ; $(RMF) contrib/SDL/atsctrb_SDL.o

cleanall:: ; make -C utils/atslex -f ./Makefile cleanall
cleanall:: ; make -C utils/atsdoc -f ./Makefile cleanall
cleanall:: ; make -C utils/scripts -f ./Makefile cleanall
cleanall:: ; make -C ccomp/runtime/GCATS -f ./Makefile cleanall

cleanall:: ; $(RMF) bootstrap1/atsopt
cleanall:: ; $(RMF) bootstrap1/atsopt_gc
cleanall:: ; make -C bootstrap0-geizella cleanall
cleanall:: ; make -C bootstrap0-anairiats cleanall

######

distclean:: cleanall
distclean:: ; find . -name .svn -prune -o -name \*~ -exec rm \{} \;

###### end of [Makefile] ######
