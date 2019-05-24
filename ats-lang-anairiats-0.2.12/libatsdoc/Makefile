#######################################################################
#                                                                     #
#                         Applied Type System                         #
#                                                                     #
#                              Hongwei Xi                             #
#                                                                     #
#######################################################################

#
# ATS/Postiats - Unleashing the Potential of Types!
# Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software
# All rights reserved
#
# ATS is  free software;  you can redistribute it and/or modify it under
# the  terms of the  GNU General Public License as published by the Free
# Software Foundation; either version 2.1, or (at your option) any later
# version.
# 
# ATS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
# for more details.
# 
# You  should  have  received  a  copy of the GNU General Public License
# along  with  ATS;  see the  file COPYING.  If not, please write to the
# Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.
#

######
#
# Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
# Start Time: August, 2011
#
######

ATSHOMEQ="$(ATSHOME)"

######

GCC=gcc

######

all:: Makefile_out
all:: ; make -f Makefile_out
all:: cleanall

######

Makefile_out: Makefile_inp ; $(GCC) -I $(ATSHOMEQ) -E -P -o $@ -x c $<

######

RMF=rm -f

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) *_?ats.o
clean:: ; $(RMF) *_?ats.c

cleanall:: clean
cleanall:: ; $(RMF) Makefile_out
cleanall:: ; $(RMF) libatsdoc.a

###### end of [Makefile] ######
