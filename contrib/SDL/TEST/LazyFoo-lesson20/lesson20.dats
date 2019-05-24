//
// LazyFoo-lesson20 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson20
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

extern
fun apply_surface {l1,l2:agz} (
    x: int, y: int, src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2, rect: &SDL_Rect
  ) : void

implement apply_surface
  (x, y, src, dst, rect) = () where {
  var offset: SDL_Rect // unintialized
  val () = SDL_Rect_init (offset, (Sint16)x, (Sint16)y, (Uint16)0, (Uint16)0)
  val _err = SDL_UpperBlit_ptr (src, &rect, dst, &offset)
} // end of [apply_surface]

(* ****** ****** *)

%{^
#define NFRAME 4
SDL_Rect clipsLeft[NFRAME] ;
SDL_Rect clipsRight[NFRAME] ;

#define FOO_WIDTH 64
#define FOO_HEIGHT 205

#define FOO_LEFT 1
#define FOO_RIGHT 0

ats_void_type
clips_init () {
  // Clip the sprites
  clipsRight[ 0 ].x = 0;
  clipsRight[ 0 ].y = 0;
  clipsRight[ 0 ].w = FOO_WIDTH;
  clipsRight[ 0 ].h = FOO_HEIGHT;

  clipsRight[ 1 ].x = FOO_WIDTH;
  clipsRight[ 1 ].y = 0;
  clipsRight[ 1 ].w = FOO_WIDTH;
  clipsRight[ 1 ].h = FOO_HEIGHT;

  clipsRight[ 2 ].x = FOO_WIDTH * 2;
  clipsRight[ 2 ].y = 0;
  clipsRight[ 2 ].w = FOO_WIDTH;
  clipsRight[ 2 ].h = FOO_HEIGHT;

  clipsRight[ 3 ].x = FOO_WIDTH * 3;
  clipsRight[ 3 ].y = 0;
  clipsRight[ 3 ].w = FOO_WIDTH;
  clipsRight[ 3 ].h = FOO_HEIGHT;

  clipsLeft[ 0 ].x = 0;
  clipsLeft[ 0 ].y = FOO_HEIGHT;
  clipsLeft[ 0 ].w = FOO_WIDTH;
  clipsLeft[ 0 ].h = FOO_HEIGHT;

  clipsLeft[ 1 ].x = FOO_WIDTH;
  clipsLeft[ 1 ].y = FOO_HEIGHT;
  clipsLeft[ 1 ].w = FOO_WIDTH;
  clipsLeft[ 1 ].h = FOO_HEIGHT;

  clipsLeft[ 2 ].x = FOO_WIDTH * 2;
  clipsLeft[ 2 ].y = FOO_HEIGHT;
  clipsLeft[ 2 ].w = FOO_WIDTH;
  clipsLeft[ 2 ].h = FOO_HEIGHT;

  clipsLeft[ 3 ].x = FOO_WIDTH * 3;
  clipsLeft[ 3 ].y = FOO_HEIGHT;
  clipsLeft[ 3 ].w = FOO_WIDTH;
  clipsLeft[ 3 ].h = FOO_HEIGHT;
} // end of [clips_init]

%}
#define NFRAME 4
typedef clips = @[SDL_Rect][NFRAME]
sta clipsLeft : addr and clipsRight : addr
val p_clipsLeft = $extval (ptr clipsLeft, "&clipsLeft[0]")
and p_clipsRight = $extval (ptr clipsRight, "&clipsRight[0]")
val () = clips_init () where {
  extern fun clips_init (): void = "clips_init"
} // end of [val]
extern prfun clipsLeft_v_get (): (clips @ clipsLeft, clips @ clipsLeft -<prf> void)
extern prfun clipsRight_v_get (): (clips @ clipsRight, clips @ clipsRight -<prf> void)

(* ****** ****** *)

//
// HX: Okay, let us do some object-oriented programming in ATS :)
//

// The dimenstions of the stick figure
macdef FOO_WIDTH = 64;
macdef FOO_HEIGHT = 205;

// The direction status of the stick figure
macdef FOO_RIGHT = 0;
macdef FOO_LEFT = 1;

%{^
typedef struct {
  ats_int_type velocity ;
  ats_int_type frame ;
  ats_int_type status ;
  struct {
    ats_int_type offset ;
  } private ;
} Foo ;
%} // end of [%{^}

abst@ype Foo_private
typedef Foo =
  $extype_struct "Foo" of {
  velocity= int
, frame= natLt (NFRAME)
, status= int
, private = Foo_private
} // end of [Foo]

extern
fun Foo_init (
    obj: &Foo? >> Foo
  , offset: int, velocity: int, frame: natLt NFRAME, status: int
  ) : void

extern
fun Foo_move (obj: &Foo): void

(* ****** ****** *)

extern
fun Foo_handle_events
  (obj: &Foo, event: &SDL_Event): void
// end of [Foo_handle_events]

(* ****** ****** *)

extern
fun Foo_show {l1,l2:agz} (
    obj: &Foo
  , foo: !SDL_Surface_ref l1, screen: !SDL_Surface_ref l2
  ) : void
// end of [Foo_show]

(* ****** ****** *)

local

assume Foo_private =
  $extype_struct "Foo" of { offset= int }
// end of [Foo_private]

in // in of [local]

implement Foo_init (
  obj, offset, velocity, frame, status
) = () where {
  val () = obj.private.offset := offset
  val () = obj.velocity := velocity
  val () = obj.frame := frame
  val () = obj.status := status
} // end of [Foo_init]

implement Foo_move (obj) = let
  val offset = obj.private.offset
  val velocity = obj.velocity
  var offset_new: int = offset + velocity
  val () = case+ 0 of
    | _ when offset_new < 0 =>
        offset_new := offset_new - velocity
    | _ when offset_new + FOO_WIDTH > SCREEN_WIDTH =>
        offset_new := offset_new - velocity
    | _ => ()
  // end of [val]
in
  obj.private.offset := offset_new
end // end of [Foo_move]

implement Foo_handle_events
  (obj, event) = let
  val _type = SDL_Event_type (event)
in
  case+ 0 of
  | _ when _type = SDL_KEYDOWN => () where {
      prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
      val sym = (&event)->keysym.sym
      prval () = view@ event := fpf (pf)
      val () = case+ 0 of
        | _ when sym = SDLK_LEFT =>
            (obj.velocity := obj.velocity - FOO_WIDTH/4)
        | _ when sym = SDLK_RIGHT =>
            (obj.velocity := obj.velocity + FOO_WIDTH/4)
        | _ => () // ignored
      // end of [val]
    } // end of [SDL_KEYDOWN]
  | _ when _type = SDL_KEYUP => () where {
      prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
      val sym = (&event)->keysym.sym
      prval () = view@ event := fpf (pf)
      val () = case+ 0 of
        | _ when sym = SDLK_LEFT =>
            (obj.velocity := obj.velocity + FOO_WIDTH/4)
        | _ when sym = SDLK_RIGHT =>
            (obj.velocity := obj.velocity - FOO_WIDTH/4)
        | _ => () // ignored
      // end of [val]
    } // end of [SDL_KEYUP]
  | _ => () // ignored
end // end of [Foo_handle_events]

implement Foo_show
  (obj, foo, screen) = let
  val velocity = obj.velocity
  val () = case+ 0 of
    | _ when velocity < 0 => () where {
        val () = obj.status := FOO_LEFT
        val frame1 = obj.frame + 1
        val () =
          if frame1 < 4 then obj.frame := frame1 else obj.frame := 0
        // end of [val]
      } // end of [velocity < 0]
    | _ when velocity > 0 => () where {
        val () = obj.status := FOO_RIGHT
        val frame1 = obj.frame + 1
        val () =
          if frame1 < 4 then obj.frame := frame1 else obj.frame := 0
        // end of [val]
      } // end of [velocity > 0]
    | _ (* velocity = 0 *) => obj.frame := 0
  // end of [val]
  val frame = obj.frame
  val status = obj.status
  val () = case+ 0 of
    | _ when status = FOO_LEFT => () where {
        prval (pf, fpf) = clipsLeft_v_get ()
        val () = apply_surface (
          obj.private.offset, SCREEN_HEIGHT - FOO_HEIGHT, foo, screen, p_clipsLeft->[frame]
        ) // end of [val]
        prval () = fpf (pf)
      } // end of [FOO_LEFT]
    | _ when status = FOO_RIGHT => () where {
        prval (pf, fpf) = clipsRight_v_get ()
        val () = apply_surface (
          obj.private.offset, SCREEN_HEIGHT - FOO_HEIGHT, foo, screen, p_clipsRight->[frame]
        ) // end of [val]
        prval () = fpf (pf)
      } // end of [FOO_RIGHT]
    | _ => () // ignored
in
  // nothing
end // end of [Foo_show]

end // end of [local]

(* ****** ****** *)

#define FRAMES_PER_SECOND 10

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val [l1:addr] (pf_screen | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
  val () = SDL_WM_SetCaption (
    stropt_some "Animation test", stropt_none
  ) // end of [val]
//
  val [l2:addr] foo = load_image ("LazyFoo-lesson20/foo.png")
  val () = assert_errmsg (ref_isnot_null foo, #LOCATION)
//
  var theFoo: Foo // uninitialized
  val () = Foo_init (theFoo, 0, 0, 0, FOO_RIGHT)
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
        val () = Foo_handle_events (theFoo, event)
        val _type = SDL_Event_type event
      in
        if (_type = SDL_QUIT) then quit := true
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
    val () = Foo_move (theFoo)
//
    // Fill the screen white
    val _err = SDL_FillRect_ptr (screen, null, white_color)
//
    val () = Foo_show (theFoo, foo, screen)
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
  val () = SDL_FreeSurface (foo)
  val _ptr = SDL_Quit_Video (pf_screen | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson20.dats] *)
