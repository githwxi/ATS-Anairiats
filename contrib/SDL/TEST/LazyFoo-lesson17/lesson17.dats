//
// LazyFoo-lesson17 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson17
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

#define FRAMES_PER_SECOND 20

(* ****** ****** *)

#define SQUARE_WIDTH 20
#define SQUARE_HEIGHT 20

(* ****** ****** *)

infix 0 +=; macdef += (x, d) = (,(x) := ,(x) + ,(d))
infix 0 -=; macdef -= (x, d) = (,(x) := ,(x) - ,(d))

(* ****** ****** *)

symintr int
overload int with int_of_Sint16
overload int with int_of_Uint16

(* ****** ****** *)

var theWall : SDL_Rect

local

val () = begin
  theWall.x := (Sint16)300
; theWall.y := (Sint16)40
; theWall.w := (Uint16)40
; theWall.h := (Uint16)400
end // end of [val]

in

val (pfbox_theWall | ()) =
  vbox_make_view_ptr {SDL_Rect} (view@ theWall | &theWall)
// end of [val]

end // end of [local]

(* ****** ****** *)

typedef Square = @{
  box= SDL_Rect, xVel= int, yVel= int
} // end of [Square]

(* ****** ****** *)

fn Square_init (
    obj: &Square? >> Square
  ) :<> void = begin
  obj.box.x := (Sint16)0;
  obj.box.y := (Sint16)0;
  obj.box.w := (Uint16)SQUARE_WIDTH;
  obj.box.h := (Uint16)SQUARE_HEIGHT;
  obj.xVel := 0;
  obj.yVel := 0;
end // end of [Square_init]

(* ****** ****** *)

fn Square_handle_input
  (obj: &Square, event: &SDL_Event): void = let
  val _type = SDL_Event_type event
in
  case+ 0 of
  | _ when _type = SDL_KEYDOWN => let
      prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
      val sym = (&event)->keysym.sym
      prval () = view@ event := fpf (pf)
    in
      case+ 0 of
      | _ when sym = SDLK_UP => obj.yVel -= SQUARE_HEIGHT/2
      | _ when sym = SDLK_DOWN => obj.yVel += SQUARE_HEIGHT/2
      | _ when sym = SDLK_LEFT => obj.xVel -= SQUARE_WIDTH/2
      | _ when sym = SDLK_RIGHT => obj.xVel += SQUARE_WIDTH/2
      | _ => () // ignored
    end // end of [SDL_KEYDOWN]
  | _ when _type = SDL_KEYUP => let
      prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
      val sym = (&event)->keysym.sym
      prval () = view@ event := fpf (pf)
    in
      case+ 0 of
      | _ when sym = SDLK_UP => obj.yVel += SQUARE_HEIGHT/2
      | _ when sym = SDLK_DOWN => obj.yVel -= SQUARE_HEIGHT/2
      | _ when sym = SDLK_LEFT => obj.xVel += SQUARE_WIDTH/2
      | _ when sym = SDLK_RIGHT => obj.xVel -= SQUARE_WIDTH/2
      | _ => () // ignored
    end // end of [SDL_KEYUP]
  | _ => () // ignored
end // end of [Square_handle_input]

(* ****** ****** *)

fn check_collision
  (A: &SDL_Rect, B: &SDL_Rect):<> bool = let
//
  val lftA = (int)A.x
  val rghA = lftA + (int)A.w
  val topA = (int)A.y
  val botA = topA + (int)A.h
//
  val lftB = (int)B.x
  val rghB = lftB + (int)B.w
  val topB = (int)B.y
  val botB = topB + (int)B.h
in
  case+ 0 of
  | _ when botA <= topB => false
  | _ when topA >= botB => false
  | _ when rghA <= lftB => false
  | _ when lftA >= rghB => false
  | _ => true
end // end of [check_collision]

fn Square_move
  (obj: &Square): void = () where {
  prval vbox pf_theWall = pfbox_theWall
  val x_old = obj.box.x
  val x_new = (int)obj.box.x + obj.xVel
  val () = obj.box.x := (Sint16)x_new
  val () = (
    if x_new < 0 orelse
       (x_new + SQUARE_WIDTH > SCREEN_WIDTH) orelse
       check_collision (obj.box, theWall)
    then begin
      obj.box.x := x_old
    end // end of [if]
  ) : void // end of [val]

  val y_old = obj.box.y
  val y_new = (int)obj.box.y + obj.yVel
  val () = obj.box.y := (Sint16)y_new
  val () = (
    if y_new < 0 orelse
       (y_new + SQUARE_HEIGHT > SCREEN_HEIGHT) orelse
       check_collision (obj.box, theWall)
    then begin
      obj.box.y := y_old
    end // end of [if]
  ) : void // end of [val]
} // end of [Square_move]

(* ****** ****** *)

fn Square_show {l1,l2:agz}
  (obj: &Square, square: !SDL_Surface_ref l1, screen: !SDL_Surface_ref l2): void =
  apply_surface ((int)obj.box.x, (int)obj.box.y, square, screen)
// end of [Square_show]

(* ****** ****** *)

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val [l1:addr] (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
  val () = SDL_WM_SetCaption (
    stropt_some "Move the square", stropt_none
  ) // end of [val]
//
  val [l2:addr] square = load_image ("LazyFoo-lesson17/square.bmp")
  val () = assert_errmsg (ref_isnot_null square, #LOCATION)
//
  var theSquare: Square // uninitialized
  val () = Square_init (theSquare)
  var fps: Timer // uninitialized
  val () = Timer_init (fps)
//
  val (pf_minus, pf_fmt | p_fmt) = SDL_Surface_format (screen)
  val bg_color = SDL_MapRGB (!p_fmt, (Uint8)0xFF, (Uint8)0xFF, (Uint8)0xFF)
  prval () = minus_addback (pf_minus, pf_fmt | screen)
//
  val (pf_minus, pf_fmt | p_fmt) = SDL_Surface_format (screen)
  val wall_color = SDL_MapRGB (!p_fmt, (Uint8)0x77, (Uint8)0x77F, (Uint8)0x77)
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
        val () = Square_handle_input (theSquare, event)
        val _type = SDL_Event_type event
      in
        if (_type = SDL_QUIT) then quit := true
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
    val () = Square_move (theSquare)
//
    // Fill the screen white
    val _err = SDL_FillRect_ptr (screen, null, bg_color)
    // Show the wall
    val _err = let
      prval vbox pf = pfbox_theWall in
      $effmask_ref (SDL_FillRect (screen, theWall, wall_color))
    end // end of [va]
//
    val () = Square_show (theSquare, square, screen)
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
  val () = SDL_FreeSurface (square)
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson17.dats] *)
