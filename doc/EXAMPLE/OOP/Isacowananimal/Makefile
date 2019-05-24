##
##
## An interesting example found at http://merd.sourceforge.net
##
## Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
## Time: November, 2010
##
##

######

ATSHOMEQ="$(ATSHOME)"
ifeq ($(ATSHOMEQ),"")
ATSHOMEQ="/usr" # default value if [ATSHOME] is undefined
endif

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

isacowananimal: \
  isacowananimal.sats isacowananimal.dats
	$(ATSCC) -g -o $@ \
  isacowananimal.sats isacowananimal.dats && ./isacowananimal

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall:: clean
	$(RMF) isacowananimal

###### end of [Makefile] ######

