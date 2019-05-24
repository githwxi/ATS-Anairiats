#
# A simple Makefile for Clutter tests
#

######

ATSCC=$(ATSHOME)/bin/atscc
GLIBFLAGS=`pkg-config glib-2.0 --cflags --libs`
CLUTTERFLAGS=`pkg-config clutter-1.0 --cflags --libs`
ATSCLUTTERLIB=$(ATSHOME)/contrib/Clutter/atsctrb_clutter.o

######

.PHONY: all
all:: checkall

######

checkall:: compall cleanall

compall:: \
  test01 \

######

test01: clutter-test01.dats
	$(ATSCC) -o test01 clutter-test01.dats $(GLIBFLAGS) $(CLUTTERFLAGS)

######

clean::
	rm -f *~
	rm -f *_?ats.c
	rm -f *_?ats.o

cleanall: clean
	rm -f test01

###### end of [Makefile] ######
