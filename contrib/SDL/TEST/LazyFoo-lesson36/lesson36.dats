//
// LazyFoo-lesson36 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson36
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

staload "contrib/GL/SATS/gl.sats"
staload "contrib/SDL/SATS/SDL.sats"

(* ****** ****** *)

staload "timer.sats"

(* ****** ****** *)

#define SCREEN_WIDTH 640
#define SCREEN_HEIGHT 480
#define SCREEN_BPP 32

(* ****** ****** *)

infix 0 +=; macdef += (x, d) = (,(x) := ,(x) + ,(d))
infix 0 -=; macdef -= (x, d) = (,(x) := ,(x) - ,(d))

(* ****** ****** *)

macdef SQUARE_WIDTH = 20
macdef SQUARE_HEIGHT = 20

typedef Square = @{
  x= int, y= int, xVel= int, yVel= int
} // end of [Square]

fn Square_init
  (obj: &Square? >> Square):<> void = begin
  obj.x := 0; obj.y := 0; obj.xVel := 0; obj.yVel := 0
end // end of [Square_init]

fn Square_handle_input
  (obj: &Square, event: &SDL_Event): void = let
  val _type = event.type
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

fn Square_move
  (obj: &Square): void = () where {
  val x_new = obj.x + obj.xVel
  val () = if
    (x_new >= 0) andalso (x_new + SQUARE_WIDTH <= SCREEN_WIDTH) then
    obj.x := x_new
  // end of [val]
  val y_new = obj.y + obj.yVel
  val () = if
    (y_new >= 0) andalso (y_new + SQUARE_HEIGHT <= SCREEN_HEIGHT) then
    obj.y := y_new
  // end of [val]
} // end of [Square_move]

(* ****** ****** *)

symintr double
overload double with double_of_int

fn Square_show
  (obj: &Square): void = () where {
  val x = obj.x and y = obj.y
  val () = glTranslatef ((GLfloat)x, (GLfloat)y, (GLfloat)0)
  val (pf_beg | ()) = glBegin (GL_QUADS)
  val () = glColor4d (1.0, 1.0, 1.0, 1.0)
  val () = glVertex3d (0.0, 0.0, 0.0)
  val () = glVertex3d ((double)SQUARE_WIDTH, 0.0, 0.0)
  val () = glVertex3d ((double)SQUARE_WIDTH, (double)SQUARE_HEIGHT, 0.0);
  val () = glVertex3d (0.0, (double)SQUARE_HEIGHT, 0.0);
  val () = glEnd (pf_beg | (*none*))
  val () = glLoadIdentity ()
} // end of [Square_move]

(* ****** ****** *)

#define FRAMES_PER_SECOND 10

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val [l1:addr] (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_OPENGL
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
//
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho
    (0.0, (double)SCREEN_WIDTH, (double)SCREEN_HEIGHT, 0.0, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
  val () = assert_errmsg (glGetError() = GL_NO_ERROR, #LOCATION)
//
  val () = SDL_WM_SetCaption (
    stropt_some "OpenGL test", stropt_none
  ) // end of [val]
//
  var theSquare : Square
  val () = Square_init (theSquare)
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
    val () = glClear(GL_COLOR_BUFFER_BIT)
    val () = Square_show (theSquare)
    val () = SDL_GL_SwapBuffers ()
//
    val _ticks = Timer_getTicks (fps)
    val _ratio = 1000 / FRAMES_PER_SECOND
    val _diff = _ratio - _ticks
    val () = if (_diff > 0) then SDL_Delay (Uint32(_diff))
  in
    // nothing
  end // end of [val]
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson36.dats] *)
