//
// LazyFoo-lesson21 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson21
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
    if ref_is_null (optimizedImage) then optimizedImage else let
      // Map the color key
      val (pf_minus, pf_fmt | p_fmt) = SDL_Surface_format (optimizedImage)
      val colorkey = SDL_MapRGB (!p_fmt, (Uint8)0, (Uint8)0xFF, (Uint8)0xFF)
      //Set all pixels of color R 0, G 0xFF, B 0xFF to be transparent
      prval () = minus_addback (pf_minus, pf_fmt | optimizedImage)
      val _err = SDL_SetColorKey (optimizedImage, SDL_SRCCOLORKEY, colorkey)
    in
      optimizedImage
    end // end of [if]
  end // end of [if]
end // end of [load_image]

(* ****** ****** *)

fn apply_surface {l1,l2:agz} (
    x: int, y: int
  , src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2
  , srcrect: &SDL_Rect
  ) : void = () where {
  var offset: SDL_Rect // unintialized
  val () = SDL_Rect_init (offset, (Sint16)x, (Sint16)y, (Uint16)0, (Uint16)0)
  val _err = SDL_UpperBlit_ptr (src, &srcrect, dst, &offset)
} // end of [apply_surface]

fn apply_surface_null {l1,l2:agz} (
    x: int, y: int, src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2
  ) : void = () where {
  var offset: SDL_Rect // unintialized
  val () = SDL_Rect_init (offset, (Sint16)x, (Sint16)y, (Uint16)0, (Uint16)0)
  val _err = SDL_UpperBlit_ptr (src, null, dst, &offset)
} // end of [apply_surface_null]

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
  apply_surface_null (obj.x, obj.y, dot, screen)
// end of [Dot_show]

(* ****** ****** *)

symintr int
overload int with int_of_Uint16

macdef LEVEL_WIDTH = 1280
macdef LEVEL_HEIGHT = 960

fn Dot_set_camera
  (obj: &Dot, cam: &SDL_Rect): void = () where {
  val x = (obj.x + DOT_WIDTH/2) - SCREEN_WIDTH/2
  val y = (obj.y + DOT_HEIGHT/2) - SCREEN_HEIGHT/2
  val () = cam.x := Sint16
    (if x < 0 then 0 else min (x, LEVEL_WIDTH - (int)cam.w))
  val () = cam.y := Sint16
    (if y < 0 then 0 else min (y, LEVEL_HEIGHT - (int)cam.h))
} // end of [Dot_set_camera]

(* ****** ****** *)

#define FRAMES_PER_SECOND 20

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
  val [l2:addr] dot = load_image ("LazyFoo-lesson21/dot.bmp")
  val () = assert_errmsg (ref_isnot_null dot, #LOCATION)
  val [l3:addr] background = load_image("LazyFoo-lesson21/bg.png")
  val () = assert_errmsg (ref_isnot_null background, #LOCATION)
//
  var theCam : SDL_Rect
  val () = SDL_Rect_init (
    theCam, (Sint16)0, (Sint16)0, (Uint16)SCREEN_WIDTH, (Uint16)SCREEN_HEIGHT
  ) // end of [val]
//
  var theDot: Dot // uninitialized
  val () = Dot_init (theDot)
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
        val () = Dot_handle_input (theDot, event)
        val _type = SDL_Event_type event
      in
        if (_type = SDL_QUIT) then quit := true
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
    val () = Dot_move (theDot)
//
    val () = Dot_set_camera (theDot, theCam)
//
    // Show the background
    val () = apply_surface( 0, 0, background, screen, theCam)
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
  val () = SDL_FreeSurface (background)
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson21.dats] *)
