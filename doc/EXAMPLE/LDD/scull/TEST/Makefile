#
# A simple Makefile
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif # end of [ifeq]

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

######

#
# HX: Please uncomment the one you want, or skip it entirely
#
ATSCCFLAGS=
#ATSCCFLAGS=-O2
#
# '-flto' enables link-time optimization such as inlining lib functions
#
#ATSCCFLAGS=-O2 -flto

######

#
# HX: Please uncomment it if you need to run GC at run-time
#
ATSGCFLAG=
#ATSGCFLAG=-D_ATS_GCATS

######

cleanall::

######

test01: test01.dats
	$(ATSCC) $(ATSGCFLAG) $(ATSCCFLAGS) -o $@ $< || touch $@
cleanall:: ; $(RMF) test01

test02: test02.dats
	$(ATSCC) $(ATSGCFLAG) $(ATSCCFLAGS) -o $@ $< || touch $@
cleanall:: ; $(RMF) test02

######
#
# HX: these are rules you may use
#

# %_sats.o: %.sats
# 	$(ATSCC) $(ATSCCFLAGS) -c $< || touch $@

# %_dats.o: %.dats
# 	$(ATSCC) $(ATSCCFLAGS) -c $< || touch $@

######

RMF=rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.o
	$(RMF) *_?ats.c

cleanall:: clean

distclean:: cleanall

###### end of [Makefile] ######
