#
# A simple Makefile
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

all:: Hello.h
all:: Hello.class
all:: libats_Hello.so

######

Hello.h: Hello.class ; javah Hello
Hello.class: Hello.java ; javac $<
Hello_dats.o: Hello.dats; $(ATSCC) -fPIC -c Hello.dats

libats_Hello.so: Hello_dats.o
	gcc -shared -o $@ -Wl,-soname,$@ $< -ldl

######

RMF=rm -f

clean:: ; $(RMF) Hello.h
clean:: ; $(RMF) Hello_dats.c Hello_dats.o

cleanall:: clean
cleanall:: ; $(RMF) libats_Hello.so
cleanall:: ; $(RMF) Hello.class

###### end of [Makefile] ######
