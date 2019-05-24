#
# A simple Makefile
#

######

ATSUSRQ="$(ATSHOME)"

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSUSRQ)/contrib
ATSCTRBGL=$(ATSCTRB)/GL/atsctrb_GL.o
ATSCTRBXR=$(ATSCTRB)/cairo/atsctrb_cairo.o
ATSCTRBGTK=$(ATSCTRB)/GTK/atsctrb_GTK.o
ATSCTRBPSLIDE=$(ATSCTRB)/atspslide/atsctrb_atspslide.o

######

all:: myslide
all:: bin/ATSforC_present
all:: bin/fib_demo

######

GTKGLEXT=`pkg-config --cflags --libs gtk+-2.0 gtkglext-1.0 gtkglext-x11-1.0`
bin/ATSforC_present: ATSforC_present.dats ; \
  $(ATSCC) -I$(ATSCTRB) -IATS$(ATSCTRB) -O3 -o $@ $< $(ATSCTRBGL) $(ATSCTRBXR) $(ATSCTRBGTK) $(ATSCTRBPSLIDE) $(GTKGLEXT)

######

ATSforC.dvi: ATSforC.tex; pslatex $<
ATSforC.ps: ATSforC.dvi; dvips -t letter -o $@ $<

##
## This for generating image data for the slide presentation
##

myslide: ATSforC.ps
	gs -r121x93 -g1024x1024 \
         -dNOPAUSE -sDEVICE=png256 \
         -sOutputFile='data/$@_'%d.png \
         -c "<</Orientation 3>> setpagedevice" \
         -q -dBATCH ATSforC.ps

######

bin/fib_demo: fib_demo.dats ; $(ATSCC) -O2 -o $@ $<

######

clean:
	rm -f *~
	rm -f *_?ats.o
	rm -f *_?ats.c
	rm -f *.aux
	rm -f *.log
	rm -f *.out
	rm -f *.dvi

cleanall: clean
	rm -f bin/fib_demo
	rm -f bin/ATSforC_present
	rm -f data/myslide_*.png

###### end of [Makefile] ######
