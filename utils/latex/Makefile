#########################################################################
##                                                                     ##
##                         Applied Type System                         ##
##                                                                     ##
##                              Hongwei Xi                             ##
##                                                                     ##
#########################################################################

##
## ATS - Unleashing the Potential of Types!
## Copyright (C) 2002-2012 Hongwei Xi, Boston University
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
## Free Software Foundation; either version 2.1, or (at your option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

## ###### ###### ##
##
## Author of the file: Likai Liu (liulk at likai dot org)
##
## ###### ###### ##

AWK := awk
BASH := bash
PDFLATEX := pdflatex

.PHONY: all clean
all:: lstatslang.sty
clean::
	rm -f lstatslang.sty keywords.txt
lstatslang.sty: lstatslang.sty.sh keywords.txt

%: %.sh
	$(BASH) $< > $@ || rm $@

all:: sample.pdf
clean::
	rm -f sample.aux sample.log sample.pdf
sample.pdf: sample.tex lstatslang.sty
	$(PDFLATEX) $<
