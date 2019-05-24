//
// LazyFoo-lesson07 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson07
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
      // Set all pixels of color R 0, G 0xFF, B 0xFF to be transparent
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
    x: int, y: int, src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2
  ) : void

implement apply_surface
  (x, y, src, dst) = () where {
  var offset: SDL_Rect // unintialized
  val () = SDL_Rect_init (offset, (Sint16)x, (Sint16)y, (Uint16)0, (Uint16)0)
  val _err = SDL_UpperBlit_ptr (src, null, dst, &offset)
} // end of [apply_surface]

(* ****** ****** *)

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
  val _err = TTF_Init ()
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val () = SDL_WM_SetCaption (
    stropt_some "TTF test", stropt_none
  ) // end of [val]
//
  val background = load_image ("LazyFoo-lesson07/background.png")
  val () = assert_errmsg (ref_isnot_null background, #LOCATION)
//
  // Open the font
  val font = TTF_OpenFont ("LazyFoo-lesson07/lazy.ttf", 28)
  val () = assert_errmsg (TTF_Font_ref_isnot_null font, #LOCATION)
//
  //The color of the font
  var textColor : SDL_Color
  val () = SDL_Color_init (textColor, (Uint8)255, (Uint8)255, (Uint8)255)
  // Render the text
  val message = TTF_RenderText_Solid
    (font, "The quick brown fox jumps over the lazy dog", textColor)
  // end of [val]
  val () = assert_errmsg (ref_isnot_null message, #LOCATION)
//
  // Apply the images to the screen
  val () = apply_surface (0, 0, background, screen)
  val () = apply_surface (0, 150, message, screen)
//
  val _err = SDL_Flip (screen)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  var quit: bool = false
  var event: SDL_Event?
  val () = while (quit = false) begin
    if SDL_PollEvent (event) > 0 then let
      prval () = opt_unsome (event)
    in
      if SDL_Event_type event = SDL_QUIT then quit := true
    end else let
      prval () = opt_unnone {SDL_Event} (event) in (*nothing*)
    end // end of [if]
  end // end of [val]
//
  val () = TTF_CloseFont (font)
  val () = SDL_FreeSurface (background)
  val () = SDL_FreeSurface (message)
  val () = TTF_Quit ()
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson07.dats] *)
