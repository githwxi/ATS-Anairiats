//
// LazyFoo-lesson08 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson08
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

stadef sfr = SDL_Surface_ref

fn show_message {l1,l2,l3:agz} (
    screen: !sfr l1, background: !sfr l2, message: !sfr l3
  ) : void = let
  val () = apply_surface (0, 0, background, screen)
  val x = (SCREEN_WIDTH - SDL_Surface_w message) / 2
  and y = (SCREEN_HEIGHT - SDL_Surface_h message) / 2
  val () = apply_surface (x, y, message, screen)
  val _err = SDL_Flip (screen)
  val () = assert_errmsg (_err = 0, #LOCATION)
in
  // nothing
end // end of [show_message]

(* ****** ****** *)

symintr int
overload int with int_of_SDL_EventType

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
    stropt_some "Press an Arrow Key", stropt_none
  ) // end of [val]
//
  val [l2:addr] background = load_image ("LazyFoo-lesson08/background.png")
  val () = assert_errmsg (ref_isnot_null background, #LOCATION)
//
  // Open the font
  val font = TTF_OpenFont ("LazyFoo-lesson08/lazy.ttf", 72)
  val () = assert_errmsg (TTF_Font_ref_isnot_null font, #LOCATION)
//
  //The color of the font
  var textColor : SDL_Color
  val () = SDL_Color_init (textColor, (Uint8)0, (Uint8)0, (Uint8)0)
  // Render the text
  val [l3_up:addr] upMessage =
    TTF_RenderText_Solid (font, "Up was pressed", textColor)
  val () = assert_errmsg (ref_isnot_null upMessage, #LOCATION)
  val [l3_down:addr] downMessage =
    TTF_RenderText_Solid (font, "Down was pressed", textColor)
  val () = assert_errmsg (ref_isnot_null downMessage, #LOCATION)
  val [l3_left:addr] leftMessage =
    TTF_RenderText_Solid (font, "Left was pressed", textColor)
  val () = assert_errmsg (ref_isnot_null leftMessage, #LOCATION)
  val [l3_right:addr] rightMessage =
    TTF_RenderText_Solid (font, "Right was pressed", textColor)
  val () = assert_errmsg (ref_isnot_null rightMessage, #LOCATION)
//
  // Apply the images to the screen
  val () = apply_surface (0, 0, background, screen)
//
  val _err = SDL_Flip (screen)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  var quit: bool = false
  var event: SDL_Event?
//  
  val () = while (quit = false) begin
    if SDL_PollEvent (event) > 0 then let
      prval () = opt_unsome (event)
      val _type = SDL_Event_type event
(*
      val () = printf ("_type = %i\n", @((int)_type))
*)
    in
      case+ 0 of
      | _ when _type = SDL_KEYDOWN => let
          prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
          val sym = (&event)->keysym.sym
          prval () = view@ event := fpf (pf)
        in
          case+ 0 of
          | _ when sym = SDLK_UP => show_message (screen, background, upMessage)
          | _ when sym = SDLK_DOWN => show_message (screen, background, downMessage)
          | _ when sym = SDLK_LEFT => show_message (screen, background, leftMessage)
          | _ when sym = SDLK_RIGHT => show_message (screen, background, rightMessage)
          | _ => ()
        end // end of [SDL_KEYDOWN]
      | _ when _type = SDL_QUIT => quit := true
      | _ => () // ignored
    end else let
      prval () = opt_unnone {SDL_Event} (event) in (*nothing*)
    end // end of [if]
  end // end of [val]
//
  val () = TTF_CloseFont (font)
  val () = SDL_FreeSurface (background)
  val () = SDL_FreeSurface (upMessage)
  val () = SDL_FreeSurface (downMessage)
  val () = SDL_FreeSurface (leftMessage)
  val () = SDL_FreeSurface (rightMessage)
  val () = TTF_Quit ()
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson08.dats] *)
