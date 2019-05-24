#
#
# Some programs involving the CAIRO drawing package
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2010
#
#


######

ATSCC=$(ATSHOME)/bin/atscc
CURLFLAGS=`curl-config --cflags --libs`
ATSCTRB=$(ATSHOME)/contrib/cURL/atsctrb_curl.o
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

######

.PHONY: all
all: checkall

######

checkall: compall cleanall
compall:: test01
compall:: test02

######

test01: cURL-test01.dats
	$(ATSCC) -o test01 $(CURLFLAGS) $(ATSCTRB) cURL-test01.dats \
     && ./test01

test02: cURL-test02.dats
	$(ATSCC) -D_ATS_MULTITHREAD -o test02 $(GTKFLAGS) $(CURLFLAGS) $(ATSCTRB) cURL-test02.dats

######

RMF=rm -f

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	$(RMF) test01
	$(RMF) test02

###### end of [Makefile] ######
