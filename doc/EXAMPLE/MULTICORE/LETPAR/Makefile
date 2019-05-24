######
#
# A simple Makefile
#
# Please use a version of ATS/Geizella (dating back to March 2008)
# to compile these examples.
#
# Note that ATS/Anairiats does not support the 'letpar' notation and
# it can thus not be used to compile these examples.
#
# HX-2011-05-02:
# the code is now obsolete; it is here mostly for telling a bit of
# history about the development of ATS.
#
######

LIBSRC := \
  thunk.sats \
  pthread.sats pthread.dats \
  pthread_locks.sats \
  parallel.sats parallel.dats

######

fib_mt: fib_mt.dats
	atscc -o fib_mt -O3 -D_ATS_MULTITHREAD -lpthread $(LIBSRC) fib_mt.dats

partial-sums_mt: partial-sums_mt.dats
	atscc -o partial-sums_mt -O3 -D_ATS_MULTITHREAD -lpthread partial-sums_mt.dats $(LIBSRC) -lm

nsieve_mt: nsieve_mt.dats
	atscc -o nsieve_mt -O3 -D_ATS_MULTITHREAD -lpthread nsieve_mt.dats $(LIBSRC) -lm

mergesort_mt_int: mergesort_mt_int.dats
	atscc -o mergesort_mt_int -O3 -D_ATS_MULTITHREAD -lpthread mergesort_mt_int.dats $(LIBSRC) -lm
mergesort_mt_flt: mergesort_mt_flt.dats
	atscc -o mergesort_mt_flt -O3 -D_ATS_MULTITHREAD -lpthread mergesort_mt_flt.dats $(LIBSRC) -lm

quicksort_mt_int: quicksort_mt_int.dats
	atscc -o quicksort_mt_int -O3 -D_ATS_MULTITHREAD -lpthread quicksort_mt_int.dats $(LIBSRC) -lm
quicksort_mt_flt: quicksort_mt_flt.dats
	atscc -o quicksort_mt_flt -O3 -D_ATS_MULTITHREAD -lpthread quicksort_mt_flt.dats $(LIBSRC) -lm

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
cleanall:: ; rm -f fib_mt
cleanall:: ; rm -f partial-sums_mt
cleanall:: ; rm -f nsieve_mt
cleanall:: ; rm -f mergesort_mt_int
cleanall:: ; rm -f mergesort_mt_flt
cleanall:: ; rm -f quicksort_mt_int
cleanall:: ; rm -f quicksort_mt_flt

###### end of [Makefile] ######
