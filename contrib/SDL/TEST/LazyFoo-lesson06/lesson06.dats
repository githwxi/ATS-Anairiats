//
// LazyFoo-lesson06 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson06
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

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
//
  val () = SDL_WM_SetCaption (
    stropt_some "Split the dots", stropt_none
  ) // end of [val]
//
  val dots = load_image ("LazyFoo-lesson06/dots.png")
  val () = assert_errmsg (ref_isnot_null dots, #LOCATION)
//
  var clip0: SDL_Rect
  val () = SDL_Rect_init (clip0, (Sint16)0, (Sint16)0, (Uint16)100, (Uint16)100)
//
  var clip1: SDL_Rect
  val () = SDL_Rect_init (clip1, (Sint16)100, (Sint16)0, (Uint16)100, (Uint16)100)
//
  var clip2: SDL_Rect
  val () = SDL_Rect_init (clip2, (Sint16)0, (Sint16)100, (Uint16)100, (Uint16)100)
//
  var clip3: SDL_Rect
  val () = SDL_Rect_init (clip3, (Sint16)100, (Sint16)100, (Uint16)100, (Uint16)100)
//
  // Fill the screen white
  val (pf_minus, pf_fmt | p_fmt) = SDL_Surface_format (screen)
  val color = SDL_MapRGB (!p_fmt, (Uint8)0xFF, (Uint8)0xFF, (Uint8)0xFF)
  prval () = minus_addback (pf_minus, pf_fmt | screen)
  val _err = SDL_FillRect_ptr (screen, null, color)
//
  // Apply the sprites to the screen
  val () = apply_surface(0, 0, dots, screen, clip0)
  val () = apply_surface(540, 0, dots, screen, clip1)
  val () = apply_surface(0, 380, dots, screen, clip2)
  val () = apply_surface(540, 380, dots, screen, clip3)
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
  val () = SDL_FreeSurface (dots)
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson06.dats] *)
