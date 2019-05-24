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
## Copyright (C) 2002-2008 Hongwei Xi.
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

all:: config.mk
all_ngc:: config.mk

######

configure : ; /bin/bash autogen.sh

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

bindir2=$(DESTDIR)$(bindir)
ATSLIBHOME2=$(DESTDIR)$(ATSLIBHOME)

######

#
# HX-2011-06-01:
# This part is by Georg Bauhaus (bauhaus AT arcor DOT de):
# It addresses the issue that the [-D] option is not available
# for $(INSTALL) on MacOSX.
#
.PHONY: install_dirs

install_dirs:: config.h
#
# make all subdirectories needed by install.
#
	cd $(abs_top_srcdir)
	[ -d $(bindir2) ] || $(MKDIR_P) $(bindir2)
	$(MKDIR_P) $(ATSLIBHOME2)/bin
	find ccomp contrib doc libats libc prelude -type d \
	  -exec $(MKDIR_P) $(ATSLIBHOME2)/\{} \; \
	  -print

install_files:: install_dirs
#
# recursively install all files in the list except .svn control files.
#
	for d in ccomp/runtime contrib doc libats libc prelude; do \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -d $(ATSLIBHOME2)/"$$d" && \
	  find "$$d" -name .svn -prune -o -type f \
            -exec $(INSTALL) -m 644 \{} $(ATSLIBHOME2)/\{} \; \
	    -print && \
	  find "$$d" -name .svn -prune -o -type l \
            -exec cp -d \{} $(ATSLIBHOME2)/\{} \; \
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
	  $(INSTALL) -m 644 "$$f" $(ATSLIBHOME2)/"$$f" && \
	  echo "$$f"; \
	done
#
# install specific files in the list as executables.
#
	for f in bin/*; do \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -m 755 "$$f" $(ATSLIBHOME2)/"$$f" && \
	  echo "$$f"; \
	done
#
# install multiple copies of wrapper script, for each binary.
#
	for f in bin/*; do \
	  b=`basename "$$f"`; \
	  cd $(abs_top_srcdir) && \
	  $(INSTALL) -m 755 ats_env.sh $(bindir2)/"$$b" && \
	  echo [ats_env.sh] is installed into $(bindir2)/"$$b"; \
	done

install:: install_files

######
#
all:: atsopt1
all:: bin_atscc
all:: bin_atslib
all:: libfiles
all:: libfiles_mt
all:: libatsdoca
all:: GCATS_gc_o
all:: GCATS_gc_mt_o
all:: atsopt1_gc
all:: bin_atspack
all:: bin_atslex
all:: bin_atsdoc
all:: atscontrib
#
all:: ; @echo "ATS/Anairiats has been built up successfully!"
all:: ; @echo "The value of ATSHOME for this build is \"$(ATSHOME)\"."
all:: ; @echo "The value of ATSHOMERELOC for this build is \"$(ATSHOMERELOC)\"."
#
######
#
all_ngc:: atsopt1
all_ngc:: bin_atscc
all_ngc:: bin_atslib
all_ngc:: libfiles
all_ngc:: libfiles_mt
all_ngc:: libatsdoca
all_ngc:: bin_atspack
all_ngc:: bin_atslex
all_ngc:: bin_atsdoc_ngc
#
all_ngc:: ; @echo "ATS/Anairiats has been built up successfully!"
all_ngc:: ; @echo "The value of ATSHOME for this build is \"$(ATSHOME)\"."
all_ngc:: ; @echo "The value of ATSHOMERELOC for this build is \"$(ATSHOMERELOC)\"."
#
###### w/o GC ######
#
atsopt1:: ; \
make -C bootstrap1 \
  -f ../Makefile_bootstrap BOOTSTRAP1=1 atsopt
#
atsopt1:: ; \
$(CPF) bootstrap1/atsopt $(ATSHOMEQ)/bin/atsopt
#
###### with GC ######
#
atsopt1_gc:: ; \
make -C bootstrap1 \
  -f ../Makefile_bootstrap BOOTSTRAP1=1 atsopt_gc
#
atsopt1_gc:: ; \
$(CPF) bootstrap1/atsopt_gc $(ATSHOMEQ)/bin/atsopt
#
###### contrib libraries ######

atscontrib::
# ifeq (1,1)
# 	$(MAKE) -C contrib/parcomb all
# endif
# ifeq ($(HAVE_LIBGLIB20),1)
# 	$(MAKE) -C contrib/glib all
# endif
# ifeq ($(HAVE_LIBGTK20),1)
# 	$(MAKE) -C contrib/cairo all
# 	$(MAKE) -C contrib/pango all
# 	$(MAKE) -C contrib/GTK all
# endif
# ifeq ($(HAVE_LIBSDL10),1)
# 	$(MAKE) -C contrib/SDL all
# endif

###### some toplevel commands ######

bin_atscc bin_atslib:
	$(MAKE) -C utils/scripts atscc
	$(CPF) utils/scripts/atscc $(ATSHOMEQ)/bin
	$(MAKE) -C utils/scripts atslib
	$(CPF) utils/scripts/atslib $(ATSHOMEQ)/bin
	$(MAKE) -C utils/scripts clean

bin_atspack:
	$(MAKE) -C utils/scripts atspack
	cp utils/scripts/atspack $(ATSHOMEQ)/bin

######
#
ATS_PROOFCHECK=
#
# ATS_PROOFCHECK=-D_ATS_PROOFCHECK # it should be turned on from time to time
#
###### library ######
#
# $(GCC) -E for preprocessing
#
GCC=gcc
ATSLIB=$(ATSHOMEQ)/bin/atslib
#
######
#
.libfiles_local: .libfiles ; $(GCC) -E -P -x c -o $@ $<
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
.libfiles_mt_local: .libfiles_mt ; $(GCC) -E -P -x c -o $@ $<
libfiles_mt: .libfiles_mt_local
	$(ATSLIB) $(ATS_PROOFCHECK) -D_ATS_MULTITHREAD -O2 --libats_mt
#
libatsdoca: ; $(MAKE) -C libatsdoc
#
###### atslex ######
#
bin_atslex: ; \
cd utils/atslex; \
$(MAKE) atslex; $(CPF) atslex $(ATSHOMEQ)/bin/atslex; $(MAKE) cleanall
#
###### atsdoc ######
#
bin_atsdoc: ; \
cd utils/atsdoc; \
$(MAKE) atsdoc; \
$(CPF) atsdoc $(ATSHOMEQ)/bin/atsdoc; \
$(MAKE) cleanall
#
bin_atsdoc_ngc: ; \
cd utils/atsdoc; \
$(MAKE) atsdoc_ngc; \
$(CPF) atsdoc_ngc $(ATSHOMEQ)/bin/atsdoc; \
$(MAKE) cleanall
#
###### GC runtime ######

GCATS_gc_o: ; cd ccomp/runtime/GCATS; $(MAKE) gc.o; $(MAKE) clean
GCATS_gc_mt_o: ; cd ccomp/runtime/GCATS; $(MAKE) gc_mt.o; $(MAKE) clean

######

CPF=cp -f
RMF=rm -f

######

clean::
	$(RMF) bootstrap1/*.o
	$(MAKE) -C utils/scripts clean
	$(MAKE) -C utils/atslex clean
	$(MAKE) -C utils/atsdoc clean
	$(MAKE) -C ccomp/runtime/GCATS clean

cleanall::
	$(RMF) bootstrap1/*.o
	$(RMF) $(BUILT_CONFIG_FILES)
	$(RMF) .libfiles_local
	$(RMF) .libfiles_mt_local
	$(RMF) bin/atsopt bin/atscc bin/atslib
	$(RMF) bin/atspack bin/atslex bin/atsdoc
	$(RMF) ccomp/lib/libats.a
	$(RMF) ccomp/lib/libats_mt.a
	$(RMF) ccomp/lib/libats_lex.a
	$(RMF) ccomp/lib/libats_smlbas.a
	$(RMF) ccomp/lib/libatsdoc.a
	$(RMF) ccomp/lib/output/*
	$(RMF) ccomp/lib64/libats.a
	$(RMF) ccomp/lib64/libats_mt.a
	$(RMF) ccomp/lib64/libats_lex.a
	$(RMF) ccomp/lib64/libats_smlbas.a
	$(RMF) ccomp/lib64/libatsdoc.a
	$(RMF) ccomp/lib64/output/*
	$(RMF) contrib/glib/atsctrb_glib.o
	$(RMF) contrib/cairo/atsctrb_cairo.o
	$(RMF) contrib/pango/atsctrb_pango.o
	$(RMF) contrib/X11/atsctrb_X11.o
	$(RMF) contrib/GTK/atsctrb_GTK.o
	$(RMF) contrib/GL/atsctrb_GL.o
	$(RMF) contrib/GL/atsctrb_glut.o
	$(RMF) contrib/GL/atsctrb_gtkglext.o
	$(RMF) contrib/SDL/atsctrb_SDL.o

cleanall:: ; $(MAKE) -C utils/atslex cleanall
cleanall:: ; $(MAKE) -C utils/scripts cleanall
cleanall:: ; $(MAKE) -C ccomp/runtime/GCATS cleanall

distclean:: cleanall
distclean:: ; find . -name .svn -prune -o -name \*~ -exec rm \{} \;

######
#
# end of [Makefile_dist]
#
######
