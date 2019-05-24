(*
** This is for showing how to use Cairo with SDL.
**
** It is translated into ATS from an example made by
** Writser Cleveringa, based upon code from Eric Windisch
** (plus minor code clean up by Chris Nystrom)
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2010
// 

(* ****** ****** *)

staload "libc/SATS/time.sats"

(* ****** ****** *)

staload MATH = "libc/SATS/math.sats"
macdef PI = $MATH.M_PI
macdef _2PI = 2 * PI
macdef sin = $MATH.sin
macdef cos = $MATH.cos

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

fn drawClock {l:agz}
  (cr: !cairo_ref l): void = () where {
//
  var t: time_t // unintialized
  val yesno = time_get_and_set (t)
  val () = assertloc (yesno)
  prval () = opt_unsome {time_t} (t)
//
  var tm: tm_struct // unintialized
  val _ptr = localtime_r (t, tm)
  val () = assert_errmsg (_ptr > null, #LOCATION)
  prval () = opt_unsome {tm_struct} (tm)
  val ss = tm.tm_sec * PI / 30
  val ms = tm.tm_min * PI / 30 // + ss / 60
  val hs = tm.tm_hour * PI / 6 + ms / 12
//
  val () = cairo_set_source_rgba (cr, 1.0, 1.0, 1.0, 1.0)
  val () = cairo_paint (cr)
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_ROUND)
  val () = cairo_set_line_width (cr, 0.1)
//
  // draw a black clock outline
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 1.0)
  val () = cairo_translate (cr, 0.5, 0.5)
  val () = cairo_arc (cr, 0.0, 0.0, 0.4, 0.0, _2PI)
  val () = cairo_stroke (cr)
//
  // draw a white dot on the current second
  val () = cairo_set_source_rgba (cr, 1.0, 1.0, 1.0, 0.6)
  val () = cairo_arc
    (cr, 0.4 * sin(ss), 0.4 * ~cos(ss), 0.05, 0.0, _2PI)
  val () = cairo_fill (cr)
//
  // draw the minutes indicator
  val () = cairo_set_source_rgba (cr, 0.2, 0.2, 1.0, 0.6)
  val () = cairo_move_to (cr, 0.0, 0.0)
  val () = cairo_line_to (cr, 0.4 * sin(ms), 0.4 * ~cos(ms))
  val () = cairo_stroke(cr)
//
  // draw the hours indicator
  val () = cairo_set_source_rgba (cr, 1.0, 0.2, 0.2, 0.6)
  val () = cairo_move_to (cr, 0.0, 0.0)
  val () = cairo_line_to (cr, 0.2 * sin(hs), 0.2 * ~cos(hs))
  val () = cairo_stroke (cr)
//
} // end of [drawClock]

(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"

(* ****** ****** *)

%{^
ats_ptr_type
clockDataRef_make (
  ats_int_type stride, ats_int_type height
) {
  void *p = calloc (stride*height, 1) ;
  if (!p) {
    fprintf (stderr, "clockDataRef_make: failed\n") ;
    exit(1) ;
  } // end of [if]
  return p ;
} // end of [clockDataRef_make]

ats_void_type
clockDataRef_free (ats_ptr_type p) { free(p); return ; }

%} // end of [%{^]

absviewtype clockDataRef
extern fun clockDataRef_make (stride: int, height: int): clockDataRef
  = "clockDataRef_make"
extern fun clockDataRef_free (x: clockDataRef): void
  = "clockDataRef_free"

(* ****** ****** *)

(*
** draw with Cairo on SDL surfaces
*)
fn drawScreen {l:agz}
  (screen: !SDL_Surface_ref l)
  : void = () where {
  // The drawing will exactly fit in the screen
  val width = SDL_Surface_w (screen)
  val height = SDL_Surface_h (screen)
  // The number of bytes used for every scanline
  val stride = 4 * width // why 4? because 32bits = 4 bytes?
  val clockDataRef = clockDataRef_make (stride, height)
  val sf = cairo_image_surface_create_for_data
    ((ptr_of)clockDataRef, CAIRO_FORMAT_ARGB32, width, height, stride) where {
    extern castfn ptr_of (x: !clockDataRef): ptr
  } // end of [val]
  // create a cairo drawing context, normalize it and draw a clock
  val cr = cairo_create (sf)
  val () = cairo_surface_destroy (sf)
  val () = cairo_scale (cr, (double_of)width, (double_of)height)
  val () = drawClock (cr)
  val () = cairo_destroy (cr)
//
  val Rmask = (Uint32)0x00ff0000U
  val Gmask = (Uint32)0x0000ff00U
  val Bmask = (Uint32)0x000000ffU
  val Amask = (Uint32)0xff000000U
//
  val clockSurface = SDL_CreateRGBSurfaceFrom (
    (ptr_of)clockDataRef
  , width, height, 32(*depth*), stride, Rmask, Gmask, Bmask, Amask
  ) where {
    extern castfn ptr_of (x: !clockDataRef): ptr
  } // end of [val]
  val () = assert_errmsg (ref_isnot_null clockSurface, #LOCATION)
//
  // blit the clock to the screen and refresh
  val _err = SDL_UpperBlit_ptr (clockSurface, null, screen, null)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val () = SDL_UpdateRect (screen, (Sint32)0, (Sint32)0, (Uint32)0, (Uint32)0)
  val () = SDL_FreeSurface (clockSurface)
  val () = clockDataRef_free (clockDataRef)
//
} // end of [drawScreen]

(* ****** ****** *)

staload "utils/timer.sats"

(* ****** ****** *)

#define SCREEN_WIDTH 480
#define SCREEN_HEIGHT 480

#define FRAMES_PER_SECOND 10

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  // Set up screen
  val (pf_scr | screen) =
    SDL_SetVideoMode_exn (SCREEN_WIDTH, SCREEN_HEIGHT, 32, SDL_SWSURFACE)
  // end of [val]
//
  val () = SDL_WM_SetCaption (
    stropt_some "ATS/SDL-cairo clock", stropt_none
  ) // end of [val]
//
  var fps: Timer // uninitialized
  val () = Timer_init (fps)
//  
  var quit: bool = false
  var event: SDL_Event?  
//
  val () = while (~quit) let
    val () = Timer_start (fps)
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
        val _type = SDL_Event_type event
      in
        if (_type = SDL_QUIT) then quit := true
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
//
    val () = drawScreen (screen)
//
    val _ticks = Timer_getTicks (fps)
    val _ratio = 1000 / FRAMES_PER_SECOND
    val _diff = _ratio - _ticks
    val () = if (_diff > 0) then SDL_Delay (Uint32(_diff))
  in
    // nothing
  end // end of [val]
//
  val _ptr =
    SDL_Quit_Video (pf_scr | screen) // [screen] should be freed by SDL_Quit
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [SDL_cairo_clock.dats] *)
