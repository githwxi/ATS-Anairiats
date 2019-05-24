INSTALL := /usr/bin/install -c
PACKAGE_TARNAME := ats-anairiats
PACKAGE_VERSION := 0.2.12

abs_top_srcdir := /home/hwxi/Research/ATS-Anairiats
prefix := /usr/local
exec_prefix := ${prefix}
bindir := ${exec_prefix}/bin

CC := gcc
AR := ar
LN_S := ln -s
INSTALL := /usr/bin/install -c
MKDIR_P := /bin/mkdir -p

CFLAGS := -g -O2
CPPFLAGS := 
LDFLAGS := 

ATSHOME := $(abs_top_srcdir)
ATSLIBHOME := $(prefix)/lib/$(PACKAGE_TARNAME)-$(PACKAGE_VERSION)
ATSHOMERELOC := ATS-$(PACKAGE_VERSION)
ATSHOMEQ := "$(ATSHOME)"

HAVE_LIBGMP := yes
HAVE_LIBGLIB20 := @HAVE_LIBGLIB20@
HAVE_LIBGTK20 := @HAVE_LIBGTK20@
HAVE_LIBSDL10 := @HAVE_LIBSDL10@
