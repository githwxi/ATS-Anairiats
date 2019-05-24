#
#
# Makefile for some examples in ATS/LF
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

all:: \
#  ATS \

all:: \
#  CallByValue \

all:: \
  ClosureConv \
  CPS \

all:: \
#  CutElimIL \

all:: \
  CutElimILL \
  HilbertCalculus \
  infprime \
  irrationality-of-sqrt2 \
  ITPT \
  KolmogorovTrans \

all:: \
#  mini-ML \
 
all:: \
  naive-set.dats \
  pigeonhole \
  PyTri \
  STLC-foas \

all:: \
#  STLC-hoas \

all:: \
  STLC-SN-foas \
  STLC-SN-hoas \

######

ATSCCFLAG=--typecheck

ATS: ; $(ATSCC) $(ATSCCFLAG) ATS.dats
BinaryTree: ; $(ATSCC) $(ATSCCFLAG) BinaryTree.dats
CallByValue: ; $(ATSCC) $(ATSCCFLAG) CallByValue.dats
ClosureConv: ; $(ATSCC) $(ATSCCFLAG) ClosureConv.dats
CPS: ; $(ATSCC) $(ATSCCFLAG) CPS.dats
CutElimIL: ; $(ATSCC) $(ATSCCFLAG) CutElimIL.dats
CutElimILL: ; $(ATSCC) $(ATSCCFLAG) CutElimILL.dats
HilbertCalculus: ; $(ATSCC) $(ATSCCFLAG) HilbertCalculus.dats
infprime: ; $(ATSCC) $(ATSCCFLAG) infprime.dats
irrationality-of-sqrt2: ; $(ATSCC) $(ATSCCFLAG) irrationality-of-sqrt2.dats
ITPT: ; $(ATSCC) $(ATSCCFLAG) ITPT.dats
KolmogorovTrans: ; $(ATSCC) $(ATSCCFLAG) KolmogorovTrans.dats
mini-ML: ; $(ATSCC) $(ATSCCFLAG) mini-ML.dats
naive-set: ; $(ATSCC) $(ATSCCFLAG) naive-set.dats
pigeonhole: ; $(ATSCC) $(ATSCCFLAG) pigeonhole.dats
PyTri: ; $(ATSCC) $(ATSCCFLAG) PyTri.dats
STLC-foas: ; $(ATSCC) $(ATSCCFLAG) STLC-foas.dats
STLC-hoas: ; $(ATSCC) $(ATSCCFLAG) STLC-hoas.dats
STLC-SN-foas: ; $(ATSCC) $(ATSCCFLAG) STLC-SN-foas.dats
STLC-SN-hoas: ; $(ATSCC) $(ATSCCFLAG) STLC-SN-hoas.dats

######

html::
#	$(ATSOPT) --posmark_html -d ATS.dats
html::
	$(ATSOPT) --posmark_html -d BinaryTree.dats > BinaryTree_dats.html
#	$(ATSOPT) --posmark_html -d CallByValue.dats > CallByValue_dats.html
html::
	$(ATSOPT) --posmark_html -d ClosureConv.dats > ClosureConv_dats.html
	$(ATSOPT) --posmark_html -d CPS.dats > CPS_dats.html
#	$(ATSOPT) --posmark_html -d CutElimIL.dats > CutElimIL_dats.html
html::
	$(ATSOPT) --posmark_html -d CutElimILL.dats > CutElimILL_dats.html
	$(ATSOPT) --posmark_html -d HilbertCalculus.dats > HilbertCalculus_dats.html
	$(ATSOPT) --posmark_html -d infprime.dats > infprime_dats.html
	$(ATSOPT) --posmark_html -d irrationality-of-sqrt2.dats > irrationality-of-sqrt2_dats.html
	$(ATSOPT) --posmark_html -d ITPT.dats > ITPT_dats.html
	$(ATSOPT) --posmark_html -d KolmogorovTrans.dats > KolmogorovTrans_dats.html
	$(ATSOPT) --posmark_html -d mini-ML.dats > mini-ML_dats.html
	$(ATSOPT) --posmark_html -d naive-set.dats > naive-set_dats.html
	$(ATSOPT) --posmark_html -d pigeonhole.dats > pigeonhole_dats.html
	$(ATSOPT) --posmark_html -d PyTri.dats > PyTri_dats.html
	$(ATSOPT) --posmark_html -d STLC-foas.dats > STLC-foas_dats.html
#	$(ATSOPT) --posmark_html -d STLC-hoas.dats > STLC-hoas_dats.html
html::
	$(ATSOPT) --posmark_html -d STLC-SN-foas.dats > STLC-SN-foas_dats.html
	$(ATSOPT) --posmark_html -d STLC-SN-hoas.dats > STLC-SN-hoas_dats.html

######

xref::
	$(ATSOPT) --posmark_xref=XREF -d \
          $(ATSHOME)/utils/xref/ats_prelude_xref.dats > /dev/null
xref::
#	$(ATSOPT) --posmark_xref=XREF -d ATS.dats
xref::
	$(ATSOPT) --posmark_xref=XREF -d BinaryTree.dats > BinaryTree_dats.html
#	$(ATSOPT) --posmark_xref=XREF -d CallByValue.dats > CallByValue_dats.html
xref::
	$(ATSOPT) --posmark_xref=XREF -d ClosureConv.dats > ClosureConv_dats.html
	$(ATSOPT) --posmark_xref=XREF -d CPS.dats > CPS_dats.html
#	$(ATSOPT) --posmark_xref=XREF -d CutElimIL.dats > CutElimIL_dats.html
xref::
	$(ATSOPT) --posmark_xref=XREF -d CutElimILL.dats > CutElimILL_dats.html
	$(ATSOPT) --posmark_xref=XREF -d HilbertCalculus.dats > HilbertCalculus_dats.html
	$(ATSOPT) --posmark_xref=XREF -d infprime.dats > infprime_dats.html
	$(ATSOPT) --posmark_xref=XREF -d irrationality-of-sqrt2.dats > irrationality-of-sqrt2_dats.html
	$(ATSOPT) --posmark_xref=XREF -d ITPT.dats > ITPT_dats.html
	$(ATSOPT) --posmark_xref=XREF -d KolmogorovTrans.dats > KolmogorovTrans_dats.html
	$(ATSOPT) --posmark_xref=XREF -d mini-ML.dats > mini-ML_dats.html
	$(ATSOPT) --posmark_xref=XREF -d naive-set.dats > naive-set_dats.html
	$(ATSOPT) --posmark_xref=XREF -d pigeonhole.dats > pigeonhole_dats.html
	$(ATSOPT) --posmark_xref=XREF -d PyTri.dats > PyTri_dats.html
	$(ATSOPT) --posmark_xref=XREF -d STLC-foas.dats > STLC-foas_dats.html
#	$(ATSOPT) --posmark_xref=XREF -d STLC-hoas.dats > STLC-hoas_dats.html
xref::
	$(ATSOPT) --posmark_xref=XREF -d STLC-SN-foas.dats > STLC-SN-foas_dats.html
	$(ATSOPT) --posmark_xref=XREF -d STLC-SN-hoas.dats > STLC-SN-hoas_dats.html

######

RMF = rm -f

######

clean::
	$(RMF) *~
	$(RMF) *_?ats.c *_?ats.o

cleanall: clean
	$(RMF) *_?ats.html
	$(RMF) XREF/*.html

###### end of [Makefile] ######
