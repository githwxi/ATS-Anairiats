#
# API for mysql in ATS
#
# Start Time: August, 2012
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
#

######

ATSHOMEQ="$(ATSHOME)"

######

ATSCC=$(ATSHOMEQ)/bin/atscc
ATSCTRB=$(ATSHOMEQ)/contrib
MYSQLCFLAGS=`mysql_config --cflags --libs`

######

all::

######

all:: atsctrb_mysql.o
atsctrb_mysql.o: mysql_dats.o ; ld -r -o $@ $^

######

mysql_dats.o: DATS/mysql.dats
	$(ATSCC) -O2 -I$(ATSCTRB) -IATS$(ATSCTRB) -o $@ -c $< $(MYSQLCFLAGS)

######

RMF=rm -f

######

all:: clean
clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c *_?ats.o

######

cleanall:: clean
cleanall:: ; $(RMF) atsctrb_mysql.o

###### end of [Makefile] ######
