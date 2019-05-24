#
#
# Some Examples in ATS involving GTK+ programming
#
#

.PHONY: all
all:  compall

ATSCC=$(or $(ATSHOME), "/usr")/bin/atscc
ATSOPT=$(or $(ATSHOME), "/usr")/bin/atsopt


checkall:: compall cleanall

compall:: HelloWorld menu sudoku

# A warm-up example
HelloWorld: HelloWorld.dats
	$(ATSCC) glib.sats gtk.sats HelloWorld.dats -o HelloWorld \
          `pkg-config --cflags --libs gtk+-2.0`

# A simple menu
menu: menu.dats
	$(ATSCC) glib.sats gtk.sats menu.dats -o menu \
          `pkg-config --cflags --libs gtk+-2.0`


# A primitive implementation of the famous sudoku game
sudoku: sudoku.dats
	$(ATSCC) glib.sats gtk.sats sudoku.dats -o sudoku \
          `pkg-config --cflags --libs gtk+-2.0`

######

DIR=$(HOME)/public_html/ATS/EXAMPLE/GTK

update::
	cp Makefile $(DIR)
	cp glib.sats glib.cats $(DIR)
	cp gtk.sats gtk.cats $(DIR)
	cp HelloWorld.dats $(DIR)
	cp menu.dats $(DIR)
	cp sudoku.dats $(DIR)

######

clean::
	rm -f *_dats.c *_sats.c *~

cleanall:: clean
	rm -f HelloWorld menu sudoku

######
