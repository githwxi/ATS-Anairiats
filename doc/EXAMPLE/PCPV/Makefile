#
#
# A simple Makefile for testing
#
# HX: ATS-0.2.4 or above is needed for testing
#

######

ATSCC=$(ATSHOME)/bin/atscc

######

all: checkall cleanall

######

checkall :: test_insort_arr
checkall :: test_insort_lst
checkall :: test_quicksort_lst
checkall :: test_mergesort_lst
checkall :: test_bsearch_arr

######

test_insort_arr: test_insort_arr.dats
	$(ATSCC) -o $@ $< && ./test_insort_arr
cleanall:: ; rm -f test_insort_arr

test_insort_lst: test_insort_lst.dats
	$(ATSCC) -o $@ $< && ./test_insort_lst
cleanall:: ; rm -f test_insort_lst

test_quicksort_lst: test_quicksort_lst.dats
	$(ATSCC) -O3 -o $@ $< && ./test_quicksort_lst
cleanall:: ; rm -f test_quicksort_lst

test_mergesort_lst: test_mergesort_lst.dats
	$(ATSCC) -O3 -o $@ $< && ./test_mergesort_lst
cleanall:: ; rm -f test_mergesort_lst

######

test_bsearch_arr: test_bsearch_arr.dats
	$(ATSCC) -o $@ $< && ./test_bsearch_arr
cleanall:: ; rm -f test_bsearch_arr

test_bsearch2_arr: test_bsearch2_arr.dats
	$(ATSCC) -o $@ $< && ./test_bsearch2_arr
cleanall:: ; rm -f test_bsearch2_arr

######

clean:
	rm -f *~
	rm -f *_?ats.c *_?ats.o

cleanall:: clean

###### end of [Makefile] ######
