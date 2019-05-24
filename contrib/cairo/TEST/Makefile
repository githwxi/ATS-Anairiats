#
#
# Some programs involving the CAIRO drawing package
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Time: December, 2009
#
#


######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.3"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSLIBQ)/contrib/cairo/atsctrb_cairo.o
XRFLAGS=`pkg-config cairo --cflags --libs`
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: test1-1
test1-1: cairo-test1-1.dats
	$(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test1-1 cairo-test1-1.png

checkall:: test1-2
test1-2: cairo-test1-2.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test1-2

######

checkall:: test2
test2: cairo-test2.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test2 cairo-test2.png


checkall:: test3
test3: cairo-test3.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) -lm && ./$@
cleanall:: ; $(RMF) test3 cairo-test3.png

checkall:: test4
test4: cairo-test4.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) -lm && ./$@
cleanall:: ; $(RMF) test4 cairo-test4.png


checkall:: test5
test5: cairo-test5.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) -lm && ./$@
cleanall:: ; $(RMF) test5 cairo-test5.png

checkall:: test6
test6: cairo-test6.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test6 cairo-test6.png

######

checkall:: test7-1
test7-1: cairo-test7-1.dats
	$(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test7-1 cairo-test7-1.png

checkall:: test7-2
test7-2: cairo-test7-2.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test7-2

######

checkall:: test8-1
test8-1: cairo-test8-1.dats
	$(ATSCC) -o $@ $< $(XRFLAGS) -lm && ./$@
cleanall:: ; $(RMF) test8-1 cairo-test8-1.png

checkall:: test8-2
test8-2: cairo-test8-2.dats
	$(ATSCC) -o $@ $< $(XRFLAGS) -lX11 -lm
cleanall:: ; $(RMF) test8-2

checkall:: test8-3
test8-3: cairo-test8-3.dats
	$(ATSCC) -o $@ $< $(GTKFLAGS) -lX11 -lm
cleanall:: ; $(RMF) test8-3

######

checkall:: test9
test9: cairo-test9.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test9

######

checkall:: test10
test10: cairo-test10.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test10 cairo-test10.ps

######

checkall:: test11
test11: cairo-test11.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test11 cairo-test11.png

######

checkall:: test12
test12: cairo-test12.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test12

######

checkall:: test13
test13: cairo-test13.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test13 cairo-test13.png

checkall:: test14
test14: cairo-test14.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test14 cairo-test14.png

checkall:: test15
test15: cairo-test15.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test15 cairo-test15.png

checkall:: test16
test16: cairo-test16.dats ; $(ATSCC) -o $@ $< $(XRFLAGS) && ./$@
cleanall:: ; $(RMF) test16 cairo-test16.png

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o

###### end of [Makefile] ######
