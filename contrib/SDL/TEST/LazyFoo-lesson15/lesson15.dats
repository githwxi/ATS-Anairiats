//
// LazyFoo-lesson15 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson15
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

staload "libc/SATS/printf.sats"

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val [_l:addr] (pf_scr | screen) = SDL_SetVideoMode
    (SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE)
  // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
//
  val () = SDL_WM_SetCaption
    (stropt_some "Frame rate test", stropt_none)
  // end of [val]
//
  val [_l:addr] image = load_image ("LazyFoo-lesson15/testing.png")
  val () = assert_errmsg (ref_isnot_null image, #LOCATION)
//
  var quit: bool = false
  var fps: Timer; val () = Timer_init (fps)
  var update: Timer; val () = Timer_init (update)
  val () = Timer_start (fps) and () = Timer_start (update)
//
  var frame: int = 0
  var event: SDL_Event?
  val () = while (~quit) let
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
        val _type = SDL_Event_type event
      in
        case+ 0 of
        | _ when _type = SDL_QUIT => quit := true
        | _ => () // ignored
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
    val () = apply_surface (0, 0, image, screen)
    val _err = SDL_Flip (screen)
    val () = assert_errmsg (_err = 0, #LOCATION)
    val () = frame := frame + 1
    val () = if Timer_getTicks (update) > 1000 then let
      #define BUFSZ 1024
      var !p_buf with pf_buf = @[byte][BUFSZ]() // uninitialized
      val _ratio = 1000.0 * frame / Timer_getTicks (fps)
      val _n = snprintf (pf_buf | p_buf, BUFSZ, "Average frame per second: %f", @(_ratio))
      val caption = __cast (p_buf) where {
        extern castfn __cast (p: ptr): String
      }
      val () = SDL_WM_SetCaption (stropt_some caption, stropt_none)
      prval () = pf_buf := bytes_v_of_strbuf_v (pf_buf)
      val () = Timer_start (update)
    in
      // nothing
    end // end of [va]
  in
    // nothing
  end // end of [val]
//
  val () = SDL_FreeSurface (image)
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson15.dats] *)
