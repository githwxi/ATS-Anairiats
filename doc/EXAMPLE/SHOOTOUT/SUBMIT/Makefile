#
#
# Makefile for SHOOTOUT submissions
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

#CC=$(HOME)/gcc-4.3.2/bin/gcc

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
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_gc
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_gcats
	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_GCATS
#	$(ATSCC) -O3 binary-trees.dats -o binary-trees -D_ATS_GCBDW

checkall:: binary-trees_smp
cleanall:: ; $(RMF) binary-trees_smp
binary-trees_smp: binary-trees_smp_dats.c
	$(ATSCC) -D_ATS_MULTITHREAD -D_ATS_GCATS -O3 -g binary-trees_smp_dats.c -o binary-trees_smp -lpthread
binary-trees_smp_dats.c: binary-trees_smp.dats
	$(ATSOPT) -o binary-trees_smp_dats.c -d binary-trees_smp.dats

checkall:: binary-trees2
cleanall:: ; $(RMF) binary-trees2
binary-trees2: binary-trees2.dats
	$(ATSCC) -O3 binary-trees2.dats -o binary-trees2 -D_ATS_GCATS

checkall:: binary-trees2_smp
cleanall:: ; $(RMF) binary-trees2_smp
binary-trees2_smp: binary-trees2_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 binary-trees2_smp.dats -o binary-trees2_smp -D_ATS_GCATS -lpthread

checkall:: binary-trees3
cleanall:: ; $(RMF) binary-trees3
binary-trees3: binary-trees3.dats
	$(ATSCC) -D_GNU_SOURCE -D_ATS_MULTITHREAD -O3 binary-trees3.dats -o binary-trees3 -D_ATS_GCATS -lpthread

######

checkall:: fannkuch
cleanall:: ; $(RMF) fannkuch
fannkuch: fannkuch.dats
	$(ATSCC) -fomit-frame-pointer -O3 fannkuch.dats -o fannkuch
fannkuch_smp: fannkuch_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer fannkuch_smp.dats -o fannkuch_smp -lpthread

checkall:: fannkuch1
cleanall:: ; $(RMF) fannkuch1
fannkuch1: fannkuch1.dats
	$(ATSCC) -fomit-frame-pointer -O3 fannkuch1.dats -o fannkuch1
checkall:: fannkuch2
cleanall:: ; $(RMF) fannkuch2
fannkuch2: fannkuch2.dats
	$(ATSCC) -fomit-frame-pointer -O3 fannkuch2.dats -o fannkuch2

checkall:: fannkuch3
cleanall:: ; $(RMF) fannkuch3
fannkuch3: fannkuch3.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer fannkuch3.dats -o fannkuch3 -lpthread -lats_mt

######

checkall:: fannkuch-redux
cleanall:: ; $(RMF) fannkuch-redux
fannkuch-redux: fannkuch-redux.dats
	$(ATSCC) -fomit-frame-pointer -O3 fannkuch-redux.dats -o fannkuch-redux

checkall:: fannkuch2-redux
cleanall:: ; $(RMF) fannkuch2-redux
fannkuch2-redux: fannkuch2-redux.dats
	$(ATSCC) -fomit-frame-pointer -O3 fannkuch2-redux.dats -o fannkuch2-redux

######

checkall:: fasta
cleanall:: ; $(RMF) fasta
fasta: fasta.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 fasta.dats -o fasta

checkall:: fasta2
cleanall:: ; $(RMF) fasta2
fasta2: fasta2.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 fasta2.dats -o fasta2

checkall:: fasta4
cleanall:: ; $(RMF) fasta4
fasta4: fasta4.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 fasta4.dats -o fasta4

######

checkall:: k-nucleotide
cleanall:: ; $(RMF) k-nucleotide
k-nucleotide: k-nucleotide.dats
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_gc
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_gcats
	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide -D_ATS_GCATS
#	$(ATSCC) -O3 k-nucleotide.dats -o k-nucleotide

checkall:: k-nucleotide1
cleanall:: ; $(RMF) k-nucleotide1
k-nucleotide1: k-nucleotide1.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o k-nucleotide1 k-nucleotide1.dats hashtable.dats

checkall:: k-nucleotide2
cleanall:: ; $(RMF) k-nucleotide2
k-nucleotide2: k-nucleotide2.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o k-nucleotide2 k-nucleotide2.dats
#	$(ATSCC) -O3 -o k-nucleotide2 k-nucleotide2.dats

checkall:: k-nucleotide3
cleanall:: ; $(RMF) k-nucleotide3
k-nucleotide3: k-nucleotide3.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o k-nucleotide3 k-nucleotide3.dats
#	$(ATSCC) -O3 -o k-nucleotide3 k-nucleotide3.dats

checkall:: k-nucleotide3_smp
cleanall:: ; $(RMF) k-nucleotide3_smp
k-nucleotide3_smp: k-nucleotide3_smp.dats
	$(ATSCC) -D_GNU_SOURCE -D_ATS_MULTITHREAD -D_ATS_GCATS -O3 -o k-nucleotide3_smp -lpthread k-nucleotide3_smp.dats

checkall:: k-nucleotide4
cleanall:: ; $(RMF) k-nucleotide4
k-nucleotide4: k-nucleotide4.dats
	$(ATSCC) -D_ATS_GCATS -O3 -o k-nucleotide4 k-nucleotide4.dats
#	$(ATSCC) -O3 k-nucleotide4.dats -o k-nucleotide4

checkall:: k-nucleotide_mset
cleanall:: ; $(RMF) k-nucleotide_mset
k-nucleotide_mset: k-nucleotide_mset.dats
	$(ATSCC) -D_ATS_GCATS -O3  -o k-nucleotide_mset k-nucleotide_mset.dats funmset_avltree.dats

######

checkall:: mandelbrot
cleanall:: ; $(RMF) mandelbrot
mandelbrot: mandelbrot.dats
	$(ATSCC) -msse2 -O3 mandelbrot.dats -o mandelbrot
checkall:: mandelbrot_simd
cleanall:: ; $(RMF) mandelbrot_simd
mandelbrot_simd: mandelbrot_simd.dats
	$(ATSCC) -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd mandelbrot_simd.dats
checkall:: mandelbrot_simd_smp
cleanall:: ; $(RMF) mandelbrot_simd_smp
mandelbrot_simd_smp: mandelbrot_simd_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o mandelbrot_simd_smp mandelbrot_simd_smp.dats -lpthread

checkall:: mandelbrot2
cleanall:: ; $(RMF) mandelbrot2
mandelbrot2: mandelbrot2.dats
	$(ATSCC) -D_GNU_SOURCE -D_ATS_MULTITHREAD -msse2 -O3 mandelbrot2.dats -o mandelbrot2 -lpthread

######

checkall:: n-body
cleanall:: ; $(RMF) n-body
n-body: n-body.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 n-body.dats -o n-body -lm
checkall:: n-body1
cleanall:: ; $(RMF) n-body1
n-body1: n-body1.dats
	$(ATSCC) -msse2 -mfpmath=sse -O3 n-body1.dats -o n-body1 -lm
checkall:: n-body_smp
cleanall:: ; $(RMF) n-body_smp
n-body_smp: n-body_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -msse2 -mfpmath=sse -O3 n-body_smp.dats -o n-body_smp -lm -lpthread

checkall:: n-body2
cleanall:: ; $(RMF) n-body2
n-body2: n-body2.dats
	$(ATSCC) -fomit-frame-pointer -msse2 -mfpmath=sse -O3 n-body2.dats -o n-body2 -lm

######

checkall:: pidigits
cleanall:: ; $(RMF) pidigits
pidigits: pidigits.dats
	$(ATSCC) -O3 -fomit-frame-pointer pidigits.dats -o pidigits -lgmp
checkall:: pidigits2
cleanall:: ; $(RMF) pidigits2
pidigits2: pidigits2.dats
	$(ATSCC) -O3 -fomit-frame-pointer pidigits2.dats -o pidigits2 -lgmp
checkall:: pidigits3
cleanall:: ; $(RMF) pidigits3
pidigits3: pidigits3.dats
	$(ATSCC) -O3 -fomit-frame-pointer pidigits3.dats -o pidigits3 -lgmp

######

checkall:: regex-dna
cleanall:: ; $(RMF) regex-dna
regex-dna: regex-dna.dats
	$(ATSCC) -D_ATS_GCATS -O3 -fomit-frame-pointer regex-dna.dats -o regex-dna -lpcre

checkall:: regex-dna_smp
cleanall:: ; $(RMF) regex-dna_smp
regex-dna_smp: regex-dna_smp.dats
	$(ATSCC) -D_ATS_MULTITHREAD -O3 -fomit-frame-pointer regex-dna_smp.dats -o regex-dna_smp -lpthread -lpcre

checkall:: regex-dna2
cleanall:: ; $(RMF) regex-dna2
regex-dna2: regex-dna2.dats
	$(ATSCC) -D_ATS_GCATS -O3 -fomit-frame-pointer regex-dna2.dats -o regex-dna2 -lpcre

######

checkall:: reverse-complement
cleanall:: ; $(RMF) reverse-complement
reverse-complement: reverse-complement.dats
	$(ATSCC) -O3 -fomit-frame-pointer reverse-complement.dats -o reverse-complement

checkall:: reverse-complement2
cleanall:: ; $(RMF) reverse-complement2
reverse-complement2: reverse-complement2.dats
	$(ATSCC) -O3 -fomit-frame-pointer reverse-complement2.dats -o reverse-complement2

checkall:: reverse-complement3
cleanall:: ; $(RMF) reverse-complement3
reverse-complement3: reverse-complement3.dats
	$(ATSCC) -O3 -fomit-frame-pointer reverse-complement3.dats -o reverse-complement3

######

checkall:: spectral-norm
cleanall:: ; $(RMF) spectral-norm
spectral-norm: spectral-norm.dats
	$(ATSCC) -O3 -fomit-frame-pointer -msse2 spectral-norm.dats -o spectral-norm -lm
checkall:: spectral-norm_smp
cleanall:: ; $(RMF) spectral-norm_smp
spectral-norm_smp: spectral-norm_smp.dats
	$(ATSCC) -D_ATS_PROOFCHECK -D_ATS_MULTITHREAD \
          -O3 -fomit-frame-pointer -msse2 spectral-norm_smp.dats -o spectral-norm_smp -lm -lpthread

checkall:: spectral-norm1
cleanall:: ; $(RMF) spectral-norm1
spectral-norm1: spectral-norm1.dats
	$(ATSCC) -O3 -fomit-frame-pointer -msse2 spectral-norm1.dats -o spectral-norm1 -lm
checkall:: spectral-norm1_simd
cleanall:: ; $(RMF) spectral-norm1_simd
spectral-norm1_simd: spectral-norm1_simd.dats
	$(ATSCC) -O3 -fomit-frame-pointer -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -o spectral-norm1_simd spectral-norm1_simd.dats -lm

# SIMD
checkall:: spectral-norm2
cleanall:: ; $(RMF) spectral-norm2
spectral-norm2: spectral-norm2.dats
	$(ATSCC) -D_ATS_PROOFCHECK -O3 -fomit-frame-pointer -msse3 spectral-norm2.dats -o spectral-norm2 -lm

# SIMD and SMP
checkall:: spectral-norm3
cleanall:: ; $(RMF) spectral-norm3
spectral-norm3: spectral-norm3.dats
	$(ATSCC) -D_GNU_SOURCE -D_ATS_MULTITHREAD -o spectral-norm3 -O3 -fomit-frame-pointer -msse3 spectral-norm3.dats -lm -lpthread

######

checkall:: thread-ring
cleanall:: ; $(RMF) thread-ring
thread-ring: thread-ring.dats
	$(ATSCC) -O3 -fomit-frame-pointer thread-ring.dats -o thread-ring -lpthread

######

RMF = rm -f

######

clean:
	$(RMF) *~
	$(RMF) *_?ats.c
	$(RMF) *_?ats.o

###### end of [Makefile] ######
