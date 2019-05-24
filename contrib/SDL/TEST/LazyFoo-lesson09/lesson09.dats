//
// LazyFoo-lesson09 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson09
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2010
//

(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"
staload "contrib/SDL/SATS/SDL_image.sats"
staload "contrib/SDL/SATS/SDL_ttf.sats"

(* ****** ****** *)

#define SCREEN_WIDTH 640
#define SCREEN_HEIGHT 480
#define SCREEN_BPP 32

(* ****** ****** *)
  
symintr int
overload int with int_of_Sint16
overload int with int_of_Uint16
overload int with int_of_SDL_EventType

(* ****** ****** *)

%{^
#define CLIP_MOUSEOVER 0
#define CLIP_MOUSEOUT 1
#define CLIP_MOUSEDOWN 2
#define CLIP_MOUSEUP 3
%} // end of [{%^]

macdef CLIP_MOUSEOVER = 0
macdef CLIP_MOUSEOUT = 1
macdef CLIP_MOUSEDOWN = 2
macdef CLIP_MOUSEUP = 3

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
    x: int, y: int, src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2, srcrect: &SDL_Rect
  ) : void

implement apply_surface
  (x, y, src, dst, srcrect) = () where {
  var offset: SDL_Rect // unintialized
  val () = SDL_Rect_init (offset, (Sint16)x, (Sint16)y, (Uint16)0, (Uint16)0)
  val _err = SDL_UpperBlit_ptr (src, &srcrect, dst, &offset)
} // end of [apply_surface]

(* ****** ****** *)

%{^
static
ats_void_type
clips_init (
  ats_ptr_type p0
) {
  SDL_Rect *clips ;
  clips = (SDL_Rect*)p0 ;
  clips[CLIP_MOUSEOVER].x = 0;
  clips[CLIP_MOUSEOVER].y = 0;
  clips[CLIP_MOUSEOVER].w = 320;
  clips[CLIP_MOUSEOVER].h = 240;

  clips[CLIP_MOUSEOUT].x = 320;
  clips[CLIP_MOUSEOUT].y = 0;
  clips[CLIP_MOUSEOUT].w = 320;
  clips[CLIP_MOUSEOUT].h = 240;

  clips[CLIP_MOUSEDOWN].x = 0;
  clips[CLIP_MOUSEDOWN].y = 240;
  clips[CLIP_MOUSEDOWN].w = 320;
  clips[CLIP_MOUSEDOWN].h = 240;

  clips[CLIP_MOUSEUP].x = 320;
  clips[CLIP_MOUSEUP].y = 240;
  clips[CLIP_MOUSEUP].w = 320;
  clips[CLIP_MOUSEUP].h = 240;
  return ;
} // end of [clips_init]

%} // end of [%{^]

typedef clips (n:int) = @[SDL_Rect][n]

extern
fun clips_init
  (clips: &(clips 4)? >> (clips 4)): void = "clips_init"
// end of [set_clips]

(* ****** ****** *)

//
// HX:
// this is done in a functional style rather than an OO style.
// if you read this code, you are probably a functional programmer
// anyway :)
//

typedef button = SDL_Rect

fn button_mouse_is_over
  (btn: &button, x: int, y: int): bool =
  if x <= (int)btn.x then false
  else if x >= (int)btn.x + (int)btn.w then false
  else if y <= (int)btn.y then false
  else if y >= (int)btn.y + (int)btn.h then false
  else true
// end of [button_mouse_is_over]

(* ****** ****** *)

fn button_handle_event (
    btn: &button, event: &SDL_Event
  ) : intBtw (~1, 4) = let
  val _type = SDL_Event_type event
in
  case+ 0 of
  | _ when _type = SDL_MOUSEMOTION => let
      prval (pf, fpf) = SDL_Event_motion_castdn (view@ event)
      val x = (&event)->x and y = (&event)->y
      prval () = view@ event := fpf (pf)
      val isover = button_mouse_is_over (btn, (int)x, (int)y)
    in
      if isover then CLIP_MOUSEOVER else CLIP_MOUSEOUT
    end // end of [SDL_MOUSEMOTION]
  | _ when _type = SDL_MOUSEBUTTONDOWN => let
      prval (pf, fpf) = SDL_Event_button_castdn (view@ event)
      val x = (&event)->x and y = (&event)->y
      prval () = view@ event := fpf (pf)
      val isover = button_mouse_is_over (btn, (int)x, (int)y)
    in
      if isover then CLIP_MOUSEDOWN else ~1 (*default*)
    end // end of [SDL_MOUSEBUTTONDOWN]
  | _ when _type = SDL_MOUSEBUTTONUP => let
      prval (pf, fpf) = SDL_Event_button_castdn (view@ event)
      val x = (&event)->x and y = (&event)->y
      prval () = view@ event := fpf (pf)
      val isover = button_mouse_is_over (btn, (int)x, (int)y)
    in
      if isover then CLIP_MOUSEUP else ~1 (*default*)
    end // end of [SDL_MOUSEBUTTONUP]
  | _ => ~1
end // end of [button_handle_event]

(* ****** ****** *)

fn button_show {l1,l2:agz} (
    btn: &button
  , buttonSheet: !SDL_Surface_ref l1
  , screen: !SDL_Surface_ref l2
  , clip: &SDL_Rect
  ) : void = () where {
(*
  val () = printf
    ("button_show: btn.x = %i and btn.y = %i\n", @((int)btn.x, (int)btn.y))
*)
  val () = apply_surface((int)btn.x, (int)btn.y, buttonSheet, screen, clip)
} // end of [button_show]

(* ****** ****** *)

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val [l1:addr] (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
//
  val () = SDL_WM_SetCaption (
    stropt_some "Button test", stropt_none
  ) // end of [val]
//
  val [l2:addr] buttonSheet = load_image ("LazyFoo-lesson09/button.png")
  val () = assert_errmsg (ref_isnot_null buttonSheet, #LOCATION)
//
  val (pf_minus, pf_fmt | p_fmt) = SDL_Surface_format (screen)
  val white_color = SDL_MapRGB (!p_fmt, (Uint8)0xFF, (Uint8)0xFF, (Uint8)0xFF)
  prval () = minus_addback (pf_minus, pf_fmt | screen)
//
  var !p_clips with pf_clips = @[SDL_Rect][4]()
  val () = clips_init (!p_clips)
  // val () = (print "clips_init is done."; print_newline ())
//
  var myButton : button
  val () = SDL_Rect_init
    (myButton, (Sint16)170, (Sint16)120, (Uint16)320, (Uint16)240)
  // end of [val]
//
  var nclip: natLt 4 = CLIP_MOUSEOUT
//
  var quit: bool = false
  var event: SDL_Event?
  val () = while (~quit) let
//
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome {SDL_Event} (event)
        val _type = event.type
        // val () = printf ("event.type = %i\n", @((int)_type))
        val () = if _type = SDL_QUIT then quit := true
      in
        continue
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
//
    val _ptr = __cast (event) where {
      extern castfn __cast (x: &SDL_Event? >> SDL_Event): ptr
    } // end of [val]
//
    val nclip_new = button_handle_event (myButton, event)
    val () = if nclip_new >= 0 then nclip := nclip_new
//
    // Fill the screen white
    val _err = SDL_FillRect_ptr (screen, null, white_color)
//
    val () = button_show (myButton, buttonSheet, screen, p_clips->[nclip])
//
// (*
    // is this buggy ?!
    val _err = SDL_Flip (screen)
    val () = assert_errmsg (_err = 0, #LOCATION)
// *)
  in
    // nothing
  end // end of [val]
//
  val () = SDL_FreeSurface (buttonSheet)
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson09.dats] *)
