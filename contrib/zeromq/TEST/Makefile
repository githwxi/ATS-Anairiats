#
# A simple Makefile
#

######

ATSHOMEQ="$(ATSHOME)"

######

ATSCC=$(ATSHOME)/bin/atscc
ATSCTRB=$(ATSHOMEQ)/contrib

######

CCFLAGS=-O2

######

all::
all:: hwserver
all:: hwclient

######

clean::
cleanall::

######

hwserver: hwserver_dats.c
	$(ATSCC) $(CCFLAGS) -I$(ATSCTRB) -o hwserver $<  $(ATSCTRB)/zeromq/atsctrb_zeromq.o -lzmq
cleanall:: ; $(RMF) hwserver

######

hwclient: hwclient_dats.c
	$(ATSCC) $(CCFLAGS) -I$(ATSCTRB) -o hwclient $<  $(ATSCTRB)/zeromq/atsctrb_zeromq.o -lzmq
cleanall:: ; $(RMF) hwclient

######

%_dats.c: %.dats ; $(ATSCC) -cc -IATS$(ATSCTRB) $<

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o *_?ats.c

######

cleanall:: clean

###### end of [Makefile] ######
