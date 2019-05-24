//
// LazyFoo-lesson02 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson02
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2010
//

(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"

(* ****** ****** *)

#define SCREEN_WIDTH 640
#define SCREEN_HEIGHT 480
#define SCREEN_BPP 32

(* ****** ****** *)

extern
fun load_image (filename: string): SDL_Surface_ref0
implement load_image (filename) = let
  val loadedImage = SDL_LoadBMP (filename)
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

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  // Set up screen
  val (pf_scr | screen) = SDL_SetVideoMode_exn
    (SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE)
//
  val () = SDL_WM_SetCaption
    (stropt_some "Hello, world!", stropt_none)
//
  val message = load_image ("LazyFoo-lesson02/hello.bmp")
  val () = assert (~ref_is_null message)
  val background = load_image ("LazyFoo-lesson02/background.bmp")
  val () = assert (~ref_is_null background)
//
  //Apply the background to the screen
  val () = apply_surface (0, 0, background, screen)
  val () = apply_surface (320, 0, background, screen)
  val () = apply_surface (0, 240, background, screen)
  val () = apply_surface (320, 240, background, screen)
//
  //Apply the message to the screen
  val () = apply_surface(180, 140, message, screen)
//
  val _err = SDL_Flip (screen)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val () = SDL_Delay ((Uint32)2000(*ms*))
//
  //Free the surfaces
  val () = SDL_FreeSurface (message)
  val () = SDL_FreeSurface (background)
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson02.dats] *)
