#
#
# for processing the ATS tutorial
#
#

######

fproc: main.dats fildescopy_dats.o
	atscc -o fproc -O3 main.dats fildescopy_dats.o

fildescopy_dats.o: fildescopy.dats
	atscc -c -O3 -o fildescopy_dats.o fildescopy.dats

######

clean::
	rm -f *~ *_?ats.c *_?ats.o

cleanall: clean
	rm -f fproc

###### end of [Makefile] ######
