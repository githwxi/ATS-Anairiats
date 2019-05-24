//
// LazyFoo-lesson12 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson12
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

#define SCREEN_WIDTH 640
#define SCREEN_HEIGHT 480
#define SCREEN_BPP 32

(* ****** ****** *)

symintr uint
overload uint with uint_of_Uint32

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
  val [l1:addr] (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
  val _err = TTF_Init ()
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val () = SDL_WM_SetCaption (
    stropt_some "Timer test", stropt_none
  ) // end of [val]
//
  val [l2:addr] background = load_image ("LazyFoo-lesson12/background.png")
  val () = assert_errmsg (ref_isnot_null background, #LOCATION)
//
  // Open the font
  val [_l:addr] font = TTF_OpenFont ("LazyFoo-lesson12/lazy.ttf", 36)
  val () = assert_errmsg (TTF_Font_ref_isnot_null font, #LOCATION)
//
  //The color of the font
  var textColor : SDL_Color
  val () = SDL_Color_init (textColor, (Uint8)0, (Uint8)0, (Uint8)0)
//
  // Render the text
  val [_l:addr] startStop = TTF_RenderText_Solid
    (font, "Press S to start or stop the timer", textColor)
  val () = assert_errmsg (ref_isnot_null startStop, #LOCATION)
//
  // Start the timer
  var running: bool = true
  var start: Uint32 = SDL_GetTicks ()
//
  var quit: bool = false
  var event: SDL_Event?
  val () = while (~quit) let
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
            | _ when sym = SDLK_s =>
                if running then
                  (running := false; start := (Uint32)0)
                else
                  (running := true; start := SDL_GetTicks ())
                // end of [if]
            | _ => () // ignored
          end // end of [SDL_KEYDOWN]
        | _ when _type = SDL_QUIT => (quit := true)
        | _ => () // ignored
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
//
    val () = apply_surface (0, 0, background, screen)
//
    val () = () where {
      val w = SDL_Surface_w (startStop)
      val () = apply_surface((SCREEN_WIDTH - w) / 2, 200, startStop, screen)
    } // end of [val]
//
    val () = if running then let
      #define BUFSZ 1024
      var !p_buf with pf_buf = @[byte][BUFSZ]() // uninitialized
      val now = SDL_GetTicks ()
      val diff = (uint)now - (uint)start
      val _n = snprintf (pf_buf | p_buf, BUFSZ, "Timer: %u", @(diff))
      val () = () where {
        extern castfn __cast (p: ptr): string
        val seconds = TTF_RenderText_Solid (font, __cast p_buf, textColor)
        val () = assert_errmsg (ref_isnot_null seconds, #LOCATION)
        val w = SDL_Surface_w (seconds)
        val () = apply_surface ((SCREEN_WIDTH - w) / 2, 50, seconds, screen)
        val () = SDL_FreeSurface (seconds)
      } // end of [where]
      prval () = pf_buf := bytes_v_of_strbuf_v (pf_buf)
    in
      // nothing
    end // end of [val]
//
    val _err = SDL_Flip (screen)
    val () = assert_errmsg (_err = 0, #LOCATION)
//
  in
    // nothing
  end // end of [val]
//
  val () = TTF_CloseFont (font)
  val () = SDL_FreeSurface (background)
  val () = SDL_FreeSurface (startStop)
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson12.dats] *)
