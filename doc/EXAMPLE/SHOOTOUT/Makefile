#
#
# Makefile for SHOOTOUT benchmarks
#
#

######

ATSUSRQ="$(ATSHOME)"
ifeq ($(ATSUSRQ),"")
ATSUSRQ="/usr"
endif

######

ATSCC=$(ATSUSRQ)/bin/atscc
ATSOPT=$(ATSUSRQ)/bin/atsopt

######

GCC=gcc

######

.PHONY: all
all:: checkall
all:: cleanall

######

checkall::
cleanall:: clean

######

checkall:: binary-trees
cleanall:: ; $(RMF) binary-trees
binary-trees: binary-trees.dats
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_gc
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_gcats
	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_GCATS

checkall:: binary-trees-ref
cleanall:: ; $(RMF) binary-trees-ref
binary-trees-ref: binary-trees-ref.dats
#	$(ATSCC) -O3 binary-trees-ref.dats -o binary-trees-ref
#	$(ATSCC) -O3 binary-trees-ref.dats -o binary-trees-ref -D_ATS_gc
#	$(ATSCC) -O3 binary-trees-ref.dats -o binary-trees-ref -D_ATS_gcats
	$(ATSCC) -O3 binary-trees-ref.dats -o binary-trees-ref -D_ATS_GCATS

checkall:: fannkuch
cleanall:: ; $(RMF) fannkuch
fannkuch: fannkuch.dats
	$(ATSCC) -O3 -fomit-frame-pointer fannkuch.dats -o fannkuch
checkall:: fannkuch_smp
cleanall:: ; $(RMF) fannkuch_smp
fannkuch_smp: fannkuch_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer fannkuch_smp.dats -o fannkuch_smp -lpthread

checkall:: fasta
cleanall:: ; $(RMF) fasta
fasta: fasta.dats; $(ATSCC) -msse2 -O3 fasta.dats -o fasta
checkall:: fasta2
cleanall:: ; $(RMF) fasta2
fasta2: fasta2.dats; $(ATSCC) -msse2 -O3 fasta2.dats -o fasta2
checkall:: fasta4
cleanall:: ; $(RMF) fasta4
fasta4: fasta4.dats; $(ATSCC) -msse2 -O3 fasta4.dats -o fasta4

checkall:: k-nucleotide
cleanall:: ; $(RMF) k-nucleotide
k-nucleotide: k-nucleotide.dats symtbl.dats
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_gc
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_gcats
	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_GCATS

checkall:: mandelbrot
cleanall:: ; $(RMF) mandelbrot
mandelbrot: mandelbrot.dats
	$(ATSCC) -O3 mandelbrot.dats -o mandelbrot
checkall:: mandelbrot_simd
cleanall:: ; $(RMF) mandelbrot_simd
mandelbrot_simd: mandelbrot_simd.dats
	$(ATSCC) -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd mandelbrot_simd.dats
checkall:: mandelbrot_simd_smp
cleanall:: ; $(RMF) mandelbrot_simd_smp
mandelbrot_simd_smp: mandelbrot_simd_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd_smp mandelbrot_simd_smp.dats -lpthread

checkall:: n-body
cleanall:: ; $(RMF) n-body
n-body: n-body.dats
	$(ATSCC) -O3 n-body.dats -o n-body -lm
checkall:: n-body2
cleanall:: ; $(RMF) n-body2
n-body2: n-body2.dats
	$(ATSCC) -fomit-frame-pointer -msse2 -mfpmath=sse -O3 n-body2.dats -o n-body2 -lm

checkall:: nsieve
cleanall:: ; $(RMF) nsieve
nsieve: nsieve.dats
	$(ATSCC) -O3 nsieve.dats -o nsieve
checkall:: nsieve-bits
cleanall:: ; $(RMF) nsieve-bits
nsieve-bits: nsieve-bits.dats
	$(ATSCC) -O3 nsieve-bits.dats -o nsieve-bits

checkall:: partial-sums
cleanall:: ; $(RMF) partial-sums
partial-sums: partial-sums.dats
	$(ATSCC) -O3 partial-sums.dats -o partial-sums -lm
checkall:: pidigits
cleanall:: ; $(RMF) pidigits
pidigits: pidigits.dats
	$(ATSCC) -O3 pidigits.dats -o pidigits -lgmp
pidigits2: pidigits2.dats
	$(ATSCC) -O3 -fomit-frame-pointer pidigits2.dats -o pidigits2 -lgmp

checkall:: recursive
cleanall:: ; $(RMF) recursive
recursive: recursive.dats
	$(ATSCC) -O3 -fomit-frame-pointer recursive.dats -o recursive

checkall:: regex-dna
cleanall:: ; $(RMF) regex-dna
regex-dna: regex-dna.dats
#	$(ATSCC) -O3 regex-dna.dats -o regex-dna -lpcre
#	$(ATSCC) -D_ATS_GCATS -O3 -fomit-frame-pointer regex-dna.dats -o regex-dna -lpcre
	$(ATSCC) -D_ATS_GCATS -O3 regex-dna.dats -o regex-dna -lpcre

checkall:: reverse-complement
cleanall:: ; $(RMF) reverse-complement
reverse-complement: reverse-complement.dats
	$(ATSCC) -O3 reverse-complement.dats -o reverse-complement

checkall:: spectral-norm
cleanall:: ; $(RMF) spectral-norm
spectral-norm: spectral-norm.dats
	$(ATSCC) -O3 spectral-norm.dats -o spectral-norm -lm

checkall:: sum-file
cleanall:: ; $(RMF) sum-file
sum-file: sum-file.dats
	$(ATSCC) -O3 sum-file.dats -o sum-file

checkall:: thread-ring
cleanall:: ; $(RMF) thread-ring
thread-ring: thread-ring.dats
	$(ATSCC) -O3 thread-ring.dats -o thread-ring -lpthread

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

###### end of [Makefile] ######
