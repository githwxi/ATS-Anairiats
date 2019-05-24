#
#
# Some programs involving SDL
#
#

######

ATSUSRQ="$(ATSHOME)"
ATSLIBQ="$(ATSHOME)"
ifeq ("$(ATSHOME)","")
ATSUSRQ="/usr"
ATSLIBQ="/usr/lib/ats-anairiats-0.2.3"
endif

######

ATSUSRQ="$(ATSHOME)"
ATSCC=$(ATSUSRQ)/bin/atscc
ATSCTRB=\
  $(ATSLIBQ)/contrib/SDL/atsctrb_SDL.o
ATSCTRB_GL=\
  $(ATSLIBQ)/contrib/GL/atsctrb_GL.o
ATSCTRB_xr=\
  $(ATSLIBQ)/contrib/X11/atsctrb_X11.o \
  $(ATSLIBQ)/contrib/cairo/atsctrb_cairo.o
SDLCFLAGS=`sdl-config --cflags`
CAIROCFLAGS=`pkg-config cairo --cflags`

######

checkall: compall cleanall

######

compall: \
  lesson01 \
  lesson02 \
  lesson04 \
  lesson05 \
  lesson06 \
  lesson07 \
  lesson08 \
  lesson09 \
  lesson10 \
  lesson11 \
  lesson12 \
  lesson13 \
  lesson14 \
  lesson15 \
  lesson16 \
  lesson17 \
  lesson18 \
  lesson20 \
  lesson21 \
  lesson26 \
  lesson27 \
  lesson36 \
  SDL_cairo_clock \
  SDL_GL_cairo_clock \

######

lesson01: LazyFoo-lesson01/lesson01.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson01 \
          LazyFoo-lesson01/lesson01.dats $(ATSCTRB) -lSDL

lesson02: LazyFoo-lesson02/lesson02.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson02 \
          LazyFoo-lesson02/lesson02.dats $(ATSCTRB) -lSDL

#
#lesson03: there is no code for lesson03
#

lesson04: LazyFoo-lesson04/lesson04.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson04 \
          LazyFoo-lesson04/lesson04.dats $(ATSCTRB) -lSDL -lSDL_image

lesson05: LazyFoo-lesson05/lesson05.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson05 \
          LazyFoo-lesson05/lesson05.dats $(ATSCTRB) -lSDL -lSDL_image

lesson06: LazyFoo-lesson06/lesson06.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson06 \
          LazyFoo-lesson06/lesson06.dats $(ATSCTRB) -lSDL -lSDL_image

lesson07: LazyFoo-lesson07/lesson07.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson07 \
          LazyFoo-lesson07/lesson07.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson08: LazyFoo-lesson08/lesson08.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson08 \
          LazyFoo-lesson08/lesson08.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson09: LazyFoo-lesson09/lesson09.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson09 \
          LazyFoo-lesson09/lesson09.dats $(ATSCTRB) -lSDL -lSDL_image

lesson10: LazyFoo-lesson10/lesson10.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson10 \
          LazyFoo-lesson10/lesson10.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson11: LazyFoo-lesson11/lesson11.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson11 \
          LazyFoo-lesson11/lesson11.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf -lSDL_mixer

lesson12: LazyFoo-lesson12/lesson12.dats
	$(ATSCC) $(SDLCFLAGS) -o lesson12 \
          LazyFoo-lesson12/lesson12.dats $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson13: LazyFoo-lesson13/lesson13.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson13 \
          LazyFoo-lesson13/lesson13.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson14: LazyFoo-lesson14/lesson14.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson14 \
          LazyFoo-lesson14/lesson14.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson15: LazyFoo-lesson15/lesson15.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson15 \
          LazyFoo-lesson15/lesson15.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image

lesson16: LazyFoo-lesson16/lesson16.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson16 \
          LazyFoo-lesson16/lesson16.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image

lesson17: LazyFoo-lesson17/lesson17.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson17 \
          LazyFoo-lesson17/lesson17.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image

lesson18: LazyFoo-lesson18/lesson18.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson18 \
          LazyFoo-lesson18/lesson18.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image

lesson20: LazyFoo-lesson20/lesson20.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson20 \
          LazyFoo-lesson20/lesson20.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image

lesson21: LazyFoo-lesson21/lesson21.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson21 \
          LazyFoo-lesson21/lesson21.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image

lesson26: LazyFoo-lesson26/lesson26.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson26 \
          LazyFoo-lesson26/lesson26.dats $(ATSCTRB) -lSDL -lSDL_image

lesson27: LazyFoo-lesson27/lesson27.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson27 \
          LazyFoo-lesson27/lesson27.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) -lSDL -lSDL_image -lSDL_ttf

lesson33: LazyFoo-lesson33/lesson33.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson33 \
          LazyFoo-lesson33/lesson33.dats $(ATSCTRB) -lSDL -lSDL_image

lesson36: LazyFoo-lesson36/lesson36.dats
	$(ATSCC) -IATS utils $(SDLCFLAGS) -o lesson36 \
          LazyFoo-lesson36/lesson36.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) $(ATSCTRB_GL) -lSDL -lGL -lglut

######

SDL_cairo_clock: SDL_cairo_clock.dats
	$(ATSCC) -IATS utils \
          $(SDLCFLAGS) $(CAIROCFLAGS) \
          -o SDL_cairo_clock \
          SDL_cairo_clock.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) $(ATSCTRB_xr) -lSDL -lcairo

######

SDL_GL_cairo_clock: SDL_GL_cairo_clock.dats
	$(ATSCC) -IATS utils \
          $(SDLCFLAGS) $(CAIROCFLAGS) \
          -o SDL_GL_cairo_clock \
          SDL_GL_cairo_clock.dats utils/timer.sats utils/timer.dats \
          $(ATSCTRB) $(ATSCTRB_GL) $(ATSCTRB_xr) -lSDL -lGL -lglut -lcairo

######

clean:
	rm -f *_?ats.c *.o *~

cleanall: clean
	rm -f lesson01
	rm -f lesson02
	rm -f lesson04
	rm -f lesson05
	rm -f lesson06
	rm -f lesson07
	rm -f lesson08
	rm -f lesson09
	rm -f lesson10
	rm -f lesson11
	rm -f lesson12
	rm -f lesson13
	rm -f lesson14
	rm -f lesson15
	rm -f lesson16
	rm -f lesson17
	rm -f lesson18
	rm -f lesson20
	rm -f lesson21
	rm -f lesson26
	rm -f lesson27
	rm -f lesson33
	rm -f lesson36
	rm -f SDL_cairo_clock
	rm -f SDL_GL_cairo_clock

###### end of [Makefile] ######
