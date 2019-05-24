//
// LazyFoo-lesson27 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson27
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2010
//

(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"
staload "contrib/SDL/SATS/SDL_image.sats"

(* ****** ****** *)

staload "timer.sats"

(* ****** ****** *)

#define SCREEN_WIDTH 640
#define SCREEN_HEIGHT 480
#define SCREEN_BPP 32

(* ****** ****** *)

extern
fun load_image (filename: string): SDL_Surface_ref0
implement load_image (filename) = let
  val loadedImage = IMG_Load (filename)
in
  if ref_is_null loadedImage then loadedImage else let
    val optimizedImage = SDL_DisplayFormat (loadedImage)
    val () = SDL_FreeSurface (loadedImage)
  in
    optimizedImage
  end // end of [if]
end // end of [load_image]

(* ****** ****** *)

extern
fun apply_surface {l1,l2:agz} (
    x: int, y: int, src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2
  ) : void

implement apply_surface
  (x, y, src, dst) = () where {
  var offset: SDL_Rect // unintialized
  val () = SDL_Rect_init (offset, (Sint16)x, (Sint16)y, (Uint16)0, (Uint16)0)
  val _err = SDL_UpperBlit_ptr (src, null, dst, &offset)
} // end of [apply_surface]

(* ****** ****** *)

macdef FRAMES_PER_SECOND = 20

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val [l1:addr] (pfscr | screen) = SDL_SetVideoMode
    (SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE)
  // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
//
  val [l2:addr] back = load_image ("LazyFoo-lesson27/fadein.png")
  val () = assert_errmsg (ref_isnot_null back, #LOCATION)
  val [l3:addr] front = load_image ("LazyFoo-lesson27/fadeout.png")
  val () = assert_errmsg (ref_isnot_null front, #LOCATION)
//
  var fps: Timer // uninitialized
  val () = Timer_init (fps)
//
  var quit: bool = false
  var event: SDL_Event? // uninitialized
  var alpha: int = SDL_ALPHA_OPAQUE
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
    val keystates = SDL_GetKeyState_null ()
    val () = if (keystates[SDLK_UP] > 0) then
      (if (alpha < SDL_ALPHA_OPAQUE) then alpha := alpha + 5)
    // end of [if]
    val () = if (keystates[SDLK_DOWN] > 0) then
      (if (alpha > SDL_ALPHA_TRANSPARENT) then alpha := alpha - 5)
    // end of [if]
    val _err = SDL_SetAlpha (front, SDL_SRCALPHA, (Uint8)alpha)
    val () = apply_surface (0, 0, back, screen)
    val () = apply_surface( 0, 0, front, screen )
    val _err = SDL_Flip (screen)
    val () = assert_errmsg (_err = 0, #LOCATION)
    val _ticks = Timer_getTicks (fps)
    val _ratio = 1000 / FRAMES_PER_SECOND
    val _diff = _ratio - _ticks
    val () = if (_diff > 0) then SDL_Delay (Uint32(_diff))
  in
    // nothing
  end // end of [val]
//
  val () = SDL_FreeSurface (back)
  val () = SDL_FreeSurface (front)
  val _ptr = SDL_Quit_Video (pfscr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson27.dats] *)
