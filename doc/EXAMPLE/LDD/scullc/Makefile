#
# A simple Makefile for building modules
#

#
# Specify flags for the module compilation.
#
EXTRA_CFLAGS = \
  -I$(ATSHOME) \
  -D_ATS_HEADER_NONE -D_ATS_PRELUDE_NONE \
  -g \
  -Wall

######

# Kernel modules
scullc-objs := main.o
scullc-objs += scullc_dats.o
scullc-objs += scullc_data_dats.o

obj-m	:= scullc.o

###### end of [Makefile] ######

