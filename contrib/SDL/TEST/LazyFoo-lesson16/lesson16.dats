//
// LazyFoo-lesson16 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson16
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

infix 0 +=; macdef += (x, d) = (,(x) := ,(x) + ,(d))
infix 0 -=; macdef -= (x, d) = (,(x) := ,(x) - ,(d))

(* ****** ****** *)

macdef DOT_WIDTH = 20
macdef DOT_HEIGHT = 20

typedef Dot = @{
  x= int, y= int, xVel= int, yVel= int
} // end of [Dot]

fn Dot_init (obj: &Dot? >> Dot):<> void = begin
  obj.x := 0; obj.y := 0; obj.xVel := 0; obj.yVel := 0
end // end of [Dot_init]

fn Dot_handle_input
  (obj: &Dot, event: &SDL_Event): void = let
  val _type = SDL_Event_type event
in
  case+ 0 of
  | _ when _type = SDL_KEYDOWN => let
      prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
      val sym = (&event)->keysym.sym
      prval () = view@ event := fpf (pf)
    in
      case+ 0 of
      | _ when sym = SDLK_UP => obj.yVel -= DOT_HEIGHT/2
      | _ when sym = SDLK_DOWN => obj.yVel += DOT_HEIGHT/2
      | _ when sym = SDLK_LEFT => obj.xVel -= DOT_WIDTH/2
      | _ when sym = SDLK_RIGHT => obj.xVel += DOT_WIDTH/2
      | _ => () // ignored
    end // end of [SDL_KEYDOWN]
  | _ when _type = SDL_KEYUP => let
      prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
      val sym = (&event)->keysym.sym
      prval () = view@ event := fpf (pf)
    in
      case+ 0 of
      | _ when sym = SDLK_UP => obj.yVel += DOT_HEIGHT/2
      | _ when sym = SDLK_DOWN => obj.yVel -= DOT_HEIGHT/2
      | _ when sym = SDLK_LEFT => obj.xVel += DOT_WIDTH/2
      | _ when sym = SDLK_RIGHT => obj.xVel -= DOT_WIDTH/2
      | _ => () // ignored
    end // end of [SDL_KEYUP]
  | _ => () // ignored
end // end of [Dot_handle_input]

(* ****** ****** *)

fn Dot_move
  (obj: &Dot): void = () where {
  val x_new = obj.x + obj.xVel
  val () = if
    (x_new >= 0) andalso (x_new + DOT_WIDTH <= SCREEN_WIDTH) then
    obj.x := x_new
  // end of [val]
  val y_new = obj.y + obj.yVel
  val () = if
    (y_new >= 0) andalso (y_new + DOT_HEIGHT <= SCREEN_HEIGHT) then
    obj.y := y_new
  // end of [val]
} // end of [Dot_move]

fn Dot_show {l1,l2:agz}
  (obj: &Dot, dot: !SDL_Surface_ref l1, screen: !SDL_Surface_ref l2): void =
  apply_surface (obj.x, obj.y, dot, screen)
// end of [Dot_show]

(* ****** ****** *)

#define FRAMES_PER_SECOND 10

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val [l1:addr] (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
  val () = SDL_WM_SetCaption (
    stropt_some "Move the dot", stropt_none
  ) // end of [val]
//
  val [l2:addr] dot = load_image ("LazyFoo-lesson16/dot.bmp")
  val () = assert_errmsg (ref_isnot_null dot, #LOCATION)
//
  var theDot: Dot // uninitialized
  val () = Dot_init (theDot)
  var fps: Timer // uninitialized
  val () = Timer_init (fps)
//
  val (pf_minus, pf_fmt | p_fmt) = SDL_Surface_format (screen)
  val white_color = SDL_MapRGB (!p_fmt, (Uint8)0xFF, (Uint8)0xFF, (Uint8)0xFF)
  prval () = minus_addback (pf_minus, pf_fmt | screen)
//
  var quit: bool = false
  var event: SDL_Event?  
//
  val () = while (~quit) let
    val () = Timer_start (fps)
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
        val () = Dot_handle_input (theDot, event)
        val _type = event.type
      in
        if (_type = SDL_QUIT) then quit := true
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
    val () = Dot_move (theDot)
//
    // Fill the screen white
    val _err = SDL_FillRect_ptr (screen, null, white_color)
//
    val () = Dot_show (theDot, dot, screen)
//
    val _err = SDL_Flip (screen)
    val () = assert_errmsg (_err = 0, #LOCATION)
//
    val _ticks = Timer_getTicks (fps)
    val _ratio = 1000 / FRAMES_PER_SECOND
    val _diff = _ratio - _ticks
    val () = if (_diff > 0) then SDL_Delay (Uint32(_diff))
  in
    // nothing
  end // end of [val]
//
  val () = SDL_FreeSurface (dot)
  val _ptr = SDL_Quit_Video (pf_scr | screen) // no-op casting
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson16.dats] *)
