######
#
# some examples in ATS involving UNIX socket programming
#
######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

######

CFLAGS=-std=gnu99 -pedantic

######

.PHONY: all
all: checkall

######

checkall: compall cleanall

######

compall:: daytime_tcpclient
daytime_tcpclient: daytime_tcpclient.dats
	$(ATSCC) $(CFLAGS) -o daytime_tcpclient daytime_tcpclient.dats

compall:: daytime_tcpserver
daytime_tcpserver: daytime_tcpserver.dats
	$(ATSCC) $(CFLAGS) -o daytime_tcpserver daytime_tcpserver.dats

######

compall:: echo_tcpclient
echo_tcpclient: echo_tcpclient.dats
	$(ATSCC) $(CFLAGS) -o echo_tcpclient echo_tcpclient.dats

compall:: echo_tcpserver
echo_tcpserver: echo_tcpserver.dats
	$(ATSCC) $(CFLAGS) -o echo_tcpserver echo_tcpserver.dats

######

compall:: echo_preforking
echo_preforking: echo_preforking.dats
	$(ATSCC) $(CFLAGS) -o echo_preforking echo_preforking.dats

######

html:: ; $(ATSOPT) --posmark_html -d daytime_tcpclient.dats > daytime_tcpclient_dats.html
html:: ; $(ATSOPT) --posmark_html -d daytime_tcpserver.dats > daytime_tcpserver_dats.html
html:: ; $(ATSOPT) --posmark_html -d echo_tcpserver.dats > echo_tcpclient_dats.html
html:: ; $(ATSOPT) --posmark_html -d echo_tcpserver.dats > echo_tcpserver_dats.html
html:: ; $(ATSOPT) --posmark_html -d echo_preforking.dats > echo_preforking_dats.html

######

xref:: ; $(ATSOPT) --posmark_xref=XREF -d \
  $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
xref:: ; $(ATSOPT) --posmark_xref=XREF -d daytime_tcpclient.dats > daytime_tcpclient_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d daytime_tcpserver.dats > daytime_tcpserver_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d echo_tcpserver.dats > echo_tcpclient_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d echo_tcpserver.dats > echo_tcpserver_dats.html
xref:: ; $(ATSOPT) --posmark_xref=XREF -d echo_preforking.dats > echo_preforking_dats.html

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
	$(RMF) ./SOCKET/*

cleanall:: clean
	$(RMF) ./XREF/*
	$(RMF) *_?ats.html
	$(RMF) daytime_tcpserver
	$(RMF) daytime_tcpclient
	$(RMF) echo_tcpserver
	$(RMF) echo_tcpclient
	$(RMF) echo_preforking

###### end of [Makefile] ######
