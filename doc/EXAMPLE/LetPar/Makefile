fib: fib.dats; atscc -o fib -O3 fib.dats

fib_mt1: fib_mt1.dats
	atscc -o fib_mt1 -O3 -DATS_MULTITHREAD -pthread -D__ATS_gc fib_mt1.dats

fib_mt2: fib_mt2.dats
	atscc -o fib_mt2 -O3 -DATS_MULTITHREAD -pthread -D__ATS_gc fib_mt2.dats letpar_old.sats letpar_old.dats

fib_mt_unlimited: fib_mt_unlimited.dats
	atscc -o fib_mt_unlimited -O3 -DATS_MULTITHREAD -pthread -D__ATS_gc fib_mt_unlimited.dats

gcd_mt: gcd_mt.dats
	atscc -o gcd_mt -O3 -DATS_MULTITHREAD -pthread gcd_mt.dats

partial-sums_mt1: partial-sums_mt1.dats
	atscc -o partial-sums_mt1 -O3 -DATS_MULTITHREAD -pthread -D__ATS_gc partial-sums_mt1.dats -lm

partial-sums_mt2: partial-sums_mt2.dats
	atscc -o partial-sums_mt2 -O3 -DATS_MULTITHREAD -pthread -D__ATS_gc partial-sums_mt2.dats letpar_old.sats letpar_old.dats -lm

nsieve_mt1: nsieve_mt1.dats
	atscc -o nsieve_mt1 -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread nsieve_mt1.dats -lm

nsieve_mt2: nsieve_mt2.dats
	atscc -o nsieve_mt2 -O3 -D__ATS_gc -DATS_MULTITHREAD -pthread nsieve_mt2.dats letpar_old.sats letpar_old.dats -lm

clean::
	rm -f *_dats.c *_sats.c *~
