######

DIR="."
OUTPUT="./OUTPUT"
FPROC="scripts/fproc"

######

HTMLFILES=\
  syntax-coloring.html \
  basics.html \
  filename-extensions.html \
  file-inclusion.html \
  compilation.html \
  ats-main.html \
  fixity.html \
  overloading.html \
  macros.html \
  function-or-closure.html \
  variadicity.html \
  tail-recursive-functions.html \
  termination-metrics.html \
  types-with-effects.html \
  templates.html \
  lists.html \
  val-and-var.html \
  call-by-reference.html \
  pointers.html \
  references.html \
  arrays-and-matrices.html \
  linear-arrays.html \
  strings.html \
  datatypes.html \
  dataprops.html \
  dataviews.html \
  dataviewtypes.html \
  pattern-matching.html \
  exceptions.html \
  higher-order-functions.html \
  lazy-evaluation.html \
  llazy-evaluation.html \
  input-and-output.html \
  ATS-and-C.html \
  programming-with-theorem-proving.html \
  casting-functions.html \
  stack-allocation.html \
  statetypes.html \
  loopcon.html \

######

tutorial_all: $(HTMLFILES)
	$(FPROC) -many $(HTMLFILES)
	scp $(OUTPUT)/tutorial_all.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

######

ones:: $(HTMLFILES)
	$(FPROC) -one syntax-coloring.html
	$(FPROC) -one basics.html
	$(FPROC) -one filename-extensions.html
	$(FPROC) -one file-inclusion.html
	$(FPROC) -one compilation.html
	$(FPROC) -one ats-main.html
	$(FPROC) -one fixity.html
	$(FPROC) -one overloading.html
	$(FPROC) -one macros.html
	$(FPROC) -one function-or-closure.html
	$(FPROC) -one variadicity.html
	$(FPROC) -one tail-recursive-functions.html
	$(FPROC) -one termination-metrics.html
	$(FPROC) -one types-with-effects.html
	$(FPROC) -one templates.html
	$(FPROC) -one lists.html
	$(FPROC) -one val-and-var.html
	$(FPROC) -one call-by-reference.html
	$(FPROC) -one pointers.html
	$(FPROC) -one references.html
	$(FPROC) -one arrays-and-matrices.html
	$(FPROC) -one linear-arrays.html
	$(FPROC) -one strings.html
	$(FPROC) -one datatypes.html
	$(FPROC) -one dataprops.html
	$(FPROC) -one dataviews.html
	$(FPROC) -one dataviewtypes.html
	$(FPROC) -one pattern-matching.html
	$(FPROC) -one exceptions.html
	$(FPROC) -one higher-order-functions.html
	$(FPROC) -one lazy-evaluation.html
	$(FPROC) -one llazy-evaluation.html
	$(FPROC) -one input-and-output.html
	$(FPROC) -one ATS-and-C.html
	$(FPROC) -one programming-with-theorem-proving.html
	$(FPROC) -one casting-functions.html
	$(FPROC) -one stack-allocation.html
	$(FPROC) -one statetypes.html
	$(FPROC) -one loopcon.html
	scp $(OUTPUT)/*.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

######

syntax-coloring::
	$(FPROC) -one syntax-coloring.html
	scp $(OUTPUT)/syntax-coloring.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

basics::
	$(FPROC) -one basics.html
	scp $(OUTPUT)/basics.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

filename-extensions::
	$(FPROC) -one filename-extensions.html
	scp $(OUTPUT)/filename-extensions.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

file-inclusion::
	$(FPROC) -one file-inclusion.html
	scp $(OUTPUT)/file-inclusion.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

compilation::
	$(FPROC) -one compilation.html
	scp $(OUTPUT)/compilation.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

ats-main::
	$(FPROC) -one ats-main.html
	scp $(OUTPUT)/ats-main.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

fixity::
	$(FPROC) -one fixity.html
	scp $(OUTPUT)/fixity.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

overloading::
	$(FPROC) -one overloading.html
	scp $(OUTPUT)/overloading.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

macros::
	$(FPROC) -one macros.html
	scp $(OUTPUT)/macros.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

function-or-closure:: function-or-closure.html
	$(FPROC) -one function-or-closure.html
	scp $(OUTPUT)/function-or-closure.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

variadicity::
	$(FPROC) -one variadicity.html
	scp $(OUTPUT)/variadicity.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

tail-recursive-functions::
	$(FPROC) -one tail-recursive-functions.html
	scp $(OUTPUT)/tail-recursive-functions.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

termination-metrics::
	$(FPROC) -one termination-metrics.html
	scp $(OUTPUT)/termination-metrics.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

types-with-effects::
	$(FPROC) -one types-with-effects.html
	scp $(OUTPUT)/types-with-effects.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

templates::
	$(FPROC) -one templates.html
	scp $(OUTPUT)/templates.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

lists::
	$(FPROC) -one lists.html
	scp $(OUTPUT)/lists.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

val-and-var::
	$(FPROC) -one val-and-var.html
	scp $(OUTPUT)/val-and-var.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

call-by-reference::
	$(FPROC) -one call-by-reference.html
	scp $(OUTPUT)/call-by-reference.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

pointers::
	$(FPROC) -one pointers.html
	scp $(OUTPUT)/pointers.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

references::
	$(FPROC) -one references.html
	scp $(OUTPUT)/references.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

arrays-and-matrices::
	$(FPROC) -one arrays-and-matrices.html
	scp $(OUTPUT)/arrays-and-matrices.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

linear-arrays::
	$(FPROC) -one linear-arrays.html
	scp $(OUTPUT)/linear-arrays.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

strings::
	$(FPROC) -one strings.html
	scp $(OUTPUT)/strings.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

datatypes:: datatypes.html
	$(FPROC) -one datatypes.html
	scp $(OUTPUT)/datatypes.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

dataprops:: dataprops.html
	$(FPROC) -one dataprops.html
	scp $(OUTPUT)/dataprops.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

dataviews::
	$(FPROC) -one dataviews.html
	scp $(OUTPUT)/dataviews.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

dataviewtypes::
	$(FPROC) -one dataviewtypes.html
	scp $(OUTPUT)/dataviewtypes.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

pattern-matching::
	$(FPROC) -one pattern-matching.html
	scp $(OUTPUT)/pattern-matching.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

exceptions::
	$(FPROC) -one exceptions.html
	scp $(OUTPUT)/exceptions.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

higher-order-functions::
	$(FPROC) -one higher-order-functions.html
	scp $(OUTPUT)/higher-order-functions.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

lazy-evaluation::
	$(FPROC) -one lazy-evaluation.html
	scp $(OUTPUT)/lazy-evaluation.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

llazy-evaluation::
	$(FPROC) -one llazy-evaluation.html
	scp $(OUTPUT)/llazy-evaluation.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

input-and-output::
	$(FPROC) -one input-and-output.html
	scp $(OUTPUT)/input-and-output.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

ATS-and-C::
	$(FPROC) -one ATS-and-C.html
	scp $(OUTPUT)/ATS-and-C.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

programming-with-theorem-proving::
	$(FPROC) -one programming-with-theorem-proving.html
	scp $(OUTPUT)/programming-with-theorem-proving.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

casting-functions::
	$(FPROC) -one casting-functions.html
	scp $(OUTPUT)/casting-functions.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

stack-allocation::
	$(FPROC) -one stack-allocation.html
	scp $(OUTPUT)/stack-allocation.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

statetypes::
	$(FPROC) -one statetypes.html
	scp $(OUTPUT)/statetypes.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

loopcon::
	$(FPROC) -one loopcon.html
	scp $(OUTPUT)/loopcon.html \
          ats-hwxi,ats-lang@web.sourceforge.net:htdocs/TUTORIAL/contents/

######

ATSHOMEQ="$(ATSHOME)"
ATSCC=$(ATSHOMEQ)/bin/atscc
ATSDOC=$(ATSHOMEQ)/bin/atsdoc

######

compall::
	$(ATSCC)  basics.dats -lm
	$(ATSCC)  ats-main.dats
	$(ATSCC)  tail-recursive-functions.dats
	$(ATSCC)  termination-metrics.dats
	$(ATSCC)  -tc templates.dats
	$(ATSCC)  -tc lists.dats
	$(ATSCC)  -tc val-and-var.dats
	$(ATSCC)  -tc pointers.dats
	$(ATSCC)  references.dats
	$(ATSCC)  arrays-and-matrices.dats
	$(ATSCC)  linear-arrays.dats
	$(ATSCC)  -tc strings.dats
	$(ATSCC)  -tc dataprops.dats
	$(ATSCC)  datatypes.dats
	$(ATSCC)  -tc dataviews.dats
	$(ATSCC)  -tc dataviewtypes.dats
	$(ATSCC)  variadicity.dats
	$(ATSCC)  -tc pattern-matching.dats
	$(ATSCC)  lazy-evaluation.dats
	$(ATSCC)  -tc llazy-evaluation.dats
	$(ATSCC)  input-and-output.dats
	$(ATSCC)  ATS-and-C.dats
	$(ATSCC)  programming-with-theorem-proving.dats
	$(ATSCC)  -tc casting-functions.dats
	$(ATSCC)  stack-allocation.dats
	$(ATSCC)  -tc loopcon.dats

######

function-or-closure_: function-or-closure_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ function-or-closure_atxt.dats -latsdoc
function-or-closure_atxt.dats: function-or-closure.atxt
	$(ATSDOC) -do $@ -i function-or-closure.atxt > function-or-closure_atxt.txt
function-or-closure.html: function-or-closure_ ; ./function-or-closure_ > $@

clean:: ; $(RMF) function-or-closure_
cleanall:: ; $(RMF) function-or-closure.html

######

datatypes_: datatypes_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ datatypes_atxt.dats -latsdoc
datatypes_atxt.dats: datatypes.atxt
	$(ATSDOC) -do $@ -i datatypes.atxt > datatypes_atxt.txt
datatypes.html: datatypes_ ; ./datatypes_ > $@

clean:: ; $(RMF) datatypes_
cleanall:: ; $(RMF) datatypes.html

######

dataprops_: dataprops_atxt.dats
	$(ATSCC) -D_ATS_GCATS -o $@ dataprops_atxt.dats -latsdoc
dataprops_atxt.dats: dataprops.atxt
	$(ATSDOC) -do $@ -i dataprops.atxt > dataprops_atxt.txt
dataprops.html: dataprops_ ; ./dataprops_ > $@

clean:: ; $(RMF) dataprops_
cleanall:: ; $(RMF) dataprops.html

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.c
clean:: ; $(RMF) *_?ats.o
clean:: ; $(RMF) *_atxt.dats

cleanall:: clean
cleanall:: ; $(RMF) *_?ats.html

###### end of [Makefile] ######
