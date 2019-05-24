######
#
# TIGERATS: A Tiger compiler written in ATS
#
# Makefile for testing the TIGERATS compiler
#
# Author: Hongwei Xi
#
# Time: Spring, 2009
#
######

GCC=gcc -m32
TIGDIR=..
TIGCOMP=$(TIGDIR)/tigcomp

######

all:: ack
all:: ack2
all:: evenodd
all:: f91
all:: fact1
all:: fact2
all:: fib1
all:: fib2
all:: fib3
all:: fib4
all:: intpair
all:: hanoi
all:: listops
all:: merge
all:: prettyprint
all:: queens0
all:: queens1
all:: queens2
all:: sum
all:: tak

######

chmod::
	chmod 644 Makefile *.tig *_tig.s

######

ack: ack.tig
	$(TIGCOMP) ack.tig > ack_tig.s
	$(GCC) -o ack ack_tig.s $(TIGDIR)/tiger_prelude.c && ./ack

ack2: ack2.tig
	$(TIGCOMP) ack2.tig > ack2_tig.s
	$(GCC) -o ack2 ack2_tig.s $(TIGDIR)/tiger_prelude.c && ./ack2

######

evenodd: evenodd.tig
	$(TIGCOMP) evenodd.tig > evenodd_tig.s
	$(GCC) -o evenodd evenodd_tig.s $(TIGDIR)/tiger_prelude.c && ./evenodd

######

f91: f91.tig
	$(TIGCOMP) f91.tig > f91_tig.s
	$(GCC) -o f91 f91_tig.s $(TIGDIR)/tiger_prelude.c && ./f91

######

fact1: fact1.tig
	$(TIGCOMP) fact1.tig > fact1_tig.s
	$(GCC) -o fact1 fact1_tig.s $(TIGDIR)/tiger_prelude.c && ./fact1

fact2: fact2.tig
	$(TIGCOMP) fact2.tig > fact2_tig.s
	$(GCC) -o fact2 fact2_tig.s $(TIGDIR)/tiger_prelude.c && ./fact2
######

fib1: fib1.tig
	$(TIGCOMP) fib1.tig > fib1_tig.s
	$(GCC) -o fib1 fib1_tig.s $(TIGDIR)/tiger_prelude.c && ./fib1

fib2: fib2.tig
	$(TIGCOMP) fib2.tig > fib2_tig.s
	$(GCC) -o fib2 fib2_tig.s $(TIGDIR)/tiger_prelude.c && ./fib2

fib3: fib3.tig
	$(TIGCOMP) fib3.tig > fib3_tig.s
	$(GCC) -o fib3 fib3_tig.s $(TIGDIR)/tiger_prelude.c && ./fib3

fib4: fib4.tig
	$(TIGCOMP) fib4.tig > fib4_tig.s
	$(GCC) -o fib4 fib4_tig.s $(TIGDIR)/tiger_prelude.c && ./fib4

######

hanoi: hanoi.tig
	$(TIGCOMP) hanoi.tig > hanoi_tig.s
	$(GCC) -o hanoi hanoi_tig.s $(TIGDIR)/tiger_prelude.c && ./hanoi

######

intpair: intpair.tig
	$(TIGCOMP) intpair.tig > intpair_tig.s
	$(GCC) -o intpair intpair_tig.s $(TIGDIR)/tiger_prelude.c

######

listops: listops.tig
	$(TIGCOMP) listops.tig > listops_tig.s
	$(GCC) -o listops listops_tig.s $(TIGDIR)/tiger_prelude.c && ./listops

######

merge: merge.tig
	$(TIGCOMP) merge.tig > merge_tig.s
	$(GCC) -o merge merge_tig.s $(TIGDIR)/tiger_prelude.c && ./merge

######

prettyprint: prettyprint.tig
	$(TIGCOMP) prettyprint.tig > prettyprint_tig.s
	$(GCC) -o prettyprint prettyprint_tig.s $(TIGDIR)/tiger_prelude.c && ./prettyprint

######

queens0: queens0.tig
	$(TIGCOMP) queens0.tig > queens0_tig.s
	$(GCC) -o queens0 queens0_tig.s $(TIGDIR)/tiger_prelude.c && ./queens0

queens1: queens1.tig
	$(TIGCOMP) queens1.tig > queens1_tig.s
	$(GCC) -o queens1 queens1_tig.s $(TIGDIR)/tiger_prelude.c && ./queens1

queens2: queens2.tig
	$(TIGCOMP) queens2.tig > queens2_tig.s
	$(GCC) -o queens2 queens2_tig.s $(TIGDIR)/tiger_prelude.c && ./queens2

######

sum: sum.tig
	$(TIGCOMP) sum.tig > sum_tig.s
	$(GCC) -o sum sum_tig.s $(TIGDIR)/tiger_prelude.c && ./sum

######

tak: tak.tig
	$(TIGCOMP) tak.tig > tak_tig.s
	$(GCC) -o tak tak_tig.s $(TIGDIR)/tiger_prelude.c && ./tak

######

MIPS32::
	$(TIGCOMP) fact1.tig > MIPS32/fact1_tig.s
	$(TIGCOMP) fact2.tig > MIPS32/fact2_tig.s
	$(TIGCOMP) fib1.tig > MIPS32/fib1_tig.s
	$(TIGCOMP) fib2.tig > MIPS32/fib2_tig.s
	$(TIGCOMP) fib3.tig > MIPS32/fib3_tig.s
	$(TIGCOMP) fib4.tig > MIPS32/fib4_tig.s
	$(TIGCOMP) hanoi.tig > MIPS32/hanoi_tig.s
	$(TIGCOMP) intpair.tig > MIPS32/intpair_tig.s
	$(TIGCOMP) listops.tig > MIPS32/listops_tig.s
	$(TIGCOMP) merge.tig > MIPS32/merge_tig.s
	$(TIGCOMP) prettyprint.tig > MIPS32/prettyprint_tig.s
	$(TIGCOMP) queens0.tig > MIPS32/queens0_tig.s
	$(TIGCOMP) queens1.tig > MIPS32/queens1_tig.s
	$(TIGCOMP) queens2.tig > MIPS32/queens2_tig.s
	$(TIGCOMP) sum.tig > MIPS32/sum_tig.s
	$(TIGCOMP) tak.tig > MIPS32/tak_tig.s

######

clean::
	rm -f ack ack2 evenodd
	rm -f f91 fact1 fact2
	rm -f fib1 fib2 fib3 fib4
	rm -f hanoi intpair listops
	rm -f merge prettyprint
	rm -f queens0 queens1 queens2
	rm -f sum tak

cleanall: clean
	rm -f *_tig.s

###### end of [Makefile] ######
