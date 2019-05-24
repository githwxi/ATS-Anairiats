#
# A simple Makefile for GTK tests
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.6"
endif # end of [ifeq]

######

ATSCC=$(ATSUSRQ)/bin/atscc
GTKFLAGS=`pkg-config gtk+-2.0 --cflags --libs`
ATSGTKLIB=$(ATSLIBQ)/contrib/GTK/atsctrb_GTK.o

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: test01
test01: gtk-test01.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test01

checkall:: test02
test02: gtk-test02.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test02

checkall:: test03
test03: gtk-test03.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test03

checkall:: test04
test04: gtk-test04.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test04

checkall:: test05
test05: gtk-test05.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test05

checkall:: test06
test06: gtk-test06.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test06

checkall:: test07
test07: gtk-test07.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test07

checkall:: test08
test08: gtk-test08.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test08

checkall:: test09
test09: gtk-test09.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test09

######

checkall:: test10
test10: gtk-test10.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test10

checkall:: test11
test11: gtk-test11.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test11

checkall:: test12
test12: gtk-test12.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test12

checkall:: test13
test13: gtk-test13.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test13

checkall:: test14
test14: gtk-test14.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test14

######

checkall:: test15-1
test15-1: gtk-test15-1.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test15-1

checkall:: test15-2
test15-2: gtk-test15-2.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test15-2

######

checkall:: test16
test16: gtk-test16.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test16

checkall:: test17
test17: gtk-test17.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test17

checkall:: test18
test18: gtk-test18.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test18

checkall:: test19
test19: gtk-test19.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS)
cleanall:: ; $(RMF) test19

######

checkall:: test20
test20: gtk-test20.dats ; $(ATSCC) -o $@ $< $(GTKFLAGS) $(ATSGTKLIB)
cleanall:: ; $(RMF) test20

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o

###### end of [Makefile] ######
