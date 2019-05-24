#
# API for cURL in ATS
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: June, 2010
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc -Wall
CURLCFLAGS=`curl-config --cflags`

######

all: atsctrb_curl.o clean

######

atsctrb_curl.o: curl_dats.o
	ld -r -o $@ curl_dats.o

######

curl_dats.o: DATS/curl.dats
	$(ATSCC) $(XRCFLAGS) -o $@ -c DATS/curl.dats

######

clean::
	rm -f *_?ats.c *_?ats.o

cleanall: clean
	rm -f atsctrb_curl.o

###### end of [Makefile] ######
