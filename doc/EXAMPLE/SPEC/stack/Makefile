#
# A simple make file
#

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSOPT=$(ATSHOMEQ)/bin/atsopt

######

.PHONY: all

all: checkall cleanall

######

checkall::
checkall:: test_list
checkall:: test_array

######

test_list:
	$(ATSCC) -o $@ stack_list.sats stack_list.dats test_list.dats && ./test_list
cleanall:: ; RMF test_list

test_array:
	$(ATSCC) -o $@ stack_array.sats stack_array.dats test_array.dats && ./test_array
cleanall:: ; RMF test_array

######

RMF=rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o
cleanall:: clean

###### end of [Makefile] ######
