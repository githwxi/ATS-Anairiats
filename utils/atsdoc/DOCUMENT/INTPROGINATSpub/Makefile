#
#
# A Simple Makefile
#
#

######

all::

######

cleanall::

######

all:: html
html: main.db
	jw -b html --output HTML/ main.db
all:: pdf
pdf: main.db; jw -b pdf --output PDF/ main.db

######

RMF=rm -f

######

clean: ; $(RMF) *~

cleanall:: clean
cleanall:: ; $(RMF) HTML/*.html
cleanall:: ; $(RMF) PDF/main.pdf

###### end of [Makefile] ######
