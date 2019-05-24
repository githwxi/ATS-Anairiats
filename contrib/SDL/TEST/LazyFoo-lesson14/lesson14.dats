//
// LazyFoo-lesson14 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson14
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2010
//

(* ****** ****** *)
//
// How to compile: see ../Makefile
//
(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"
staload "contrib/SDL/SATS/SDL_image.sats"
staload "contrib/SDL/SATS/SDL_ttf.sats"

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
  val [_l:addr] (pf_scr | screen) = SDL_SetVideoMode
    (SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE)
  // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
//
  val _err = TTF_Init ()
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val () = SDL_WM_SetCaption
    (stropt_some "Frame Rate Test", stropt_none)
  // end of [val]
//
  val [_l:addr] background = load_image ("LazyFoo-lesson14/background.png")
  val () = assert_errmsg (ref_isnot_null background, #LOCATION)
//
  // Open the font
  val font = TTF_OpenFont ("LazyFoo-lesson14/lazy.ttf", 50)
  val () = assert_errmsg (ref_isnot_null font, #LOCATION)
//
  var quit: bool = false;
  var frame: int = 0
  var cap: bool = true
  var fps: Timer // uninitialized
  val () = Timer_init (fps)
//
  var textColor : SDL_Color
  val () = SDL_Color_init (textColor, (Uint8)0, (Uint8)0, (Uint8)0)
  val [_l:addr] message = TTF_RenderText_Solid (font, "Testing frame rate", textColor)
  val () = assert_errmsg (ref_isnot_null message, #LOCATION)
//
  var event: SDL_Event?
  val () = while (~quit) let
    val () = Timer_start (fps)
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
        val _type = SDL_Event_type event
      in
        case+ 0 of
        | _ when _type = SDL_KEYDOWN => let
            prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
            var sym = (&event)->keysym.sym
            prval () = view@ event := fpf (pf)
          in
            case+ 0 of
            | _ when sym = SDLK_RETURN => cap := ~cap
            | _ => () // ignored
          end // end of [SDL_KEYDOWN]
        | _ when _type = SDL_QUIT => quit := true
        | _ => () // ignored
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
    // Apply the background
    val () = apply_surface (0, 0, background, screen)
    // Apply the message
    val () = let
      val w = SDL_Surface_w message and h = SDL_Surface_h message
    in
      apply_surface (
        (SCREEN_WIDTH - w)/2
      , ((SCREEN_HEIGHT + 2*h)/FRAMES_PER_SECOND) * (frame mod FRAMES_PER_SECOND ) - h
      , message
      , screen
      ) // end of [apply_surface]
    end // end of [val]
//
    val _err = SDL_Flip (screen)
    val () = assert_errmsg (_err = 0, #LOCATION)
//
    val () = frame := frame + 1
    val () = if cap then let
      val _ticks = Timer_getTicks (fps)
      val _ratio = 1000 / FRAMES_PER_SECOND
    in
      if _ticks < _ratio then SDL_Delay (Uint32(_ratio - _ticks))
    end // end of [val]
  in
    // nothing
  end // end of [val]
//
  val () = TTF_CloseFont (font)
  val () = TTF_Quit ()
  val () = SDL_FreeSurface (message)
  val () = SDL_FreeSurface (background)
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson14.dats] *)
