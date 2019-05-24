#
# A simple Makefile for building modules
#

######

ATSCC=$(ATSHOME)/bin/atscc
ATSOPT=$(ATSHOME)/bin/atsopt

######

KVERS = $(shell uname -r)

######

# Kernel modules
obj-m += hello_mod_dats.o

#
# Specify flags for the module compilation.
#
EXTRA_CFLAGS += -I$(ATSHOME)
EXTRA_CFLAGS += -D_ATS_HEADER_NONE -D_ATS_PRELUDE_NONE
EXTRA_CFLAGS += -g

######

build:: hello_mod_dats.c
build:: kernel_modules

######

hello_mod_dats.c: hello_mod.dats ; make -f Makefile_src all

######

kernel_modules:
	make -C /lib/modules/$(KVERS)/build M=$(CURDIR) modules

######

clean:: ; rm -f *~
clean:: ; rm -f *_?ats.c *_?ats.o
clean:: ; make -C /lib/modules/$(KVERS)/build M=$(CURDIR) clean

###### end of [Makefile] ######
