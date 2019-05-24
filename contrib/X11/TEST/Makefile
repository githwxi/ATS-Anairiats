#
#
# Some programs involving Xlib programming
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

ATSCC="$(ATSUSRQ)"/bin/atscc
ATSCTRB="$(ATSLIBQ)"/contrib/X11/atsctrb_X11.o

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: test01
cleanall:: ; $(RMF) test01
test01: Xlib-test01.dats
	$(ATSCC) -o test01 Xlib-test01.dats $(ATSCTRB) -lX11

cleanall:: ; $(RMF) test02
test02: Xlib-test02.dats
	$(ATSCC) -o test02 Xlib-test02.dats $(ATSCTRB) -lX11

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
