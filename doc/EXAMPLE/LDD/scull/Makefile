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
scull-objs := main.o
scull-objs += scull_dats.o
scull-objs += scull_data_dats.o
scull-objs += pipe.o
scull-objs += access.o

obj-m	:= scull.o

###### end of [Makefile] ######

