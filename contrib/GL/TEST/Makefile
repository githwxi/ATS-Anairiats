#
#
# Some programs involving OpenGL
#
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.5"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=$(ATSLIBQ)/contrib/GL/atsctrb_GL.o

######

.PHONY:: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: test01
cleanall:: ; $(RMF) test01
test01: GL-test01.dats
	$(ATSCC) -o test01 GL-test01.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test02
cleanall:: ; $(RMF) test02
test02: GL-test02.dats
	$(ATSCC) -o test02 GL-test02.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test03-1
cleanall:: ; $(RMF) test03-1
test03-1: GL-test03-1.dats
	$(ATSCC) -o test03-1 GL-test03-1.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test03-2
cleanall:: ; $(RMF) test03-2
test03-2: GL-test03-2.dats
	$(ATSCC) -o test03-2 GL-test03-2.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

checkall:: test04
cleanall:: ; $(RMF) test04
test04: GL-test04.dats
	$(ATSCC) -o test04 GL-test04.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test05
cleanall:: ; $(RMF) test05
test05: GL-test05.dats
	$(ATSCC) -o test05 GL-test05.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test06
cleanall:: ; $(RMF) test06
test06: GL-test06.dats
	$(ATSCC) -O3 -o test06 GL-test06.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test07
cleanall:: ; $(RMF) test07
test07: GL-test07.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o test07 GL-test07.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

checkall:: test08
cleanall:: ; $(RMF) test08
test08: GL-test08.dats
	$(ATSCC) -O3 -o test08 GL-test08.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

checkall:: test09
cleanall:: ; $(RMF) test09
test09: GL-test09.dats
	$(ATSCC) -O3 -o test09 GL-test09.dats $(ATSCTRB) -lGL -lGLU -lglut

######

checkall:: test10
cleanall:: ; $(RMF) test10
test10: GL-test10.dats
	$(ATSCC) -O3 -o test10 GL-test10.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test11
cleanall:: ; $(RMF) test11
test11: GL-test11.dats
	$(ATSCC) -O3 -o test11 GL-test11.dats $(ATSCTRB) -lGL -lGLU -lglut -lm

checkall:: test12
cleanall:: ; $(RMF) test12
test12: GL-test12.dats
	$(ATSCC) -g -o test12 GL-test12.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test13
cleanall:: ; $(RMF) test13
test13: GL-test13.dats
	$(ATSCC) -g -o test13 GL-test13.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test14
cleanall:: ; $(RMF) test14
test14: GL-test14.dats
	$(ATSCC) -g -o test14 GL-test14.dats $(ATSCTRB) -lGL -lGLU -lglut

checkall:: test15
cleanall:: ; $(RMF) test15
test15: GL-test15.dats
	$(ATSCC) -g -o test15 GL-test15.dats $(ATSCTRB) -lGL -lGLU -lglut

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
