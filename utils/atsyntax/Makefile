##
## for highlighting/xreferencing ATS code
##

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc

######

ATSCCFLAGS=-O2 -g

######

OBJECTS := ats2xhtml_sats.o ats2xhtml_dats.o

######

atsyntax.o: $(OBJECTS) ; ld -r -o $@ $(OBJECTS)

######

%_sats.o: SATS/%.sats ; $(ATSCC) $(ATSCCFLAGS) -c $<
%_dats.o: DATS/%.dats ; $(ATSCC) $(ATSCCFLAGS) -c $<

######

RMF=rm -f

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o
clean:: ; $(RMF) *_?ats.c

cleanall:: clean
cleanall:: ; $(RMF) atsyntax.o

###### end of [Makefile] ######
