//
// LazyFoo-lesson04 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson04
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

//
// HX: I hate this style!
//
var screen
  : SDL_Surface_ref0 = SDL_Surface_ref_null ()
// end of [screen]

extern
fun init (
    pf: !SDL_Surface_ref0 @ screen | (*none*)
  ) : bool = "init"

implement init (pf | (*none*)) = let
  var ret: bool = true
  val () = if ret then
    ret := (SDL_Init (SDL_INIT_EVERYTHING) = 0)
  val () = if ret then let
    val _screen = screen
    val () = assert (ref_is_null _screen)
    val _ptr = ref_free_null (_screen)
    val (pf_scr | scr) = SDL_SetVideoMode (
      SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
    )
    prval () = __leak (pf_scr) where {
      extern prfun __leak {l:addr} (pf: Video_v l): void
    }
    val () = screen := scr
  in
    ret := ref_isnot_null (screen)
  end // end of [val]
  val () = if ret then
    SDL_WM_SetCaption (stropt_some "Event test", stropt_none)
  // end of [val]
in
  ret
end // end of [init]

(* ****** ****** *)

//
// HX: I hate this style!
//
var image
  : SDL_Surface_ref0 = SDL_Surface_ref_null ()
// end of [image]

extern
fun load_files (
    pf: !SDL_Surface_ref0 @ image | (*none*)
  ) : bool = "load_files"

implement load_files (pf | (*none*)) = let
  var ret: bool = true
  val _image = image
  val () = assert (ref_is_null _image)
  val _ = ref_free_null (_image)
  val () = image := load_image ("LazyFoo-lesson04/x.png")
  val () = ret := ref_isnot_null (image)
in
  ret
end // end of [load_files]

(* ****** ****** *)

//
// HX: I hate this style!
//
extern
fun clean_up (
    pf: !SDL_Surface_ref0 @ image | (*none*)
  ) : void = "clean_up"

implement clean_up (pf | (*none*)) = let
  val _image = image
  val () = assert (ref_isnot_null _image)
  val () = SDL_FreeSurface (_image)
  val () = image := SDL_Surface_ref_null ()
in
  SDL_Quit ()
end // end of [clean_up]

(* ****** ****** *)

extern
fun __main {l1,l2:agz} (
    pf_screen:
      !SDL_Surface_ref l1 @ screen
  , pf_image: !SDL_Surface_ref l2 @ image
  | (*none*)
  ) : void = "__main"

implement __main
  (pf_screen, pf_image | (*none*)) = () where {
  var quit: bool = false
//
  extern fun init (): bool = "init"
  val () = if (init () = false) then (
    print "__main: init: failed"; print_newline (); exit (1)
  ) // end of [if]
  extern fun load_files (): bool = "load_files"
  val () = if (load_files () = false) then (
    print "__main: load_files: failed"; print_newline (); exit (1)
  ) // end of [if]
//
  // Apply the surface to the screen
  val () = apply_surface (0, 0, image, screen)
//
  val _err = SDL_Flip (screen)
  val () = if (_err <> 0) then exit (1)
//
  var event: SDL_Event?
  val () = while (~quit) begin
    if SDL_PollEvent (event) > 0 then let
      prval () = opt_unsome (event)
    in
      if SDL_Event_type event = SDL_QUIT then quit := true
    end else let
      prval () = opt_unnone {SDL_Event} (event) in (*nothing*)
    end // end of [if]
  end // end of [val]
(*
  val () = (
    print "__main: quit = "; print quit; print_newline ()
  ) // end of [val]
*)
  extern fun clean_up (): void = "clean_up"
  val () = clean_up ()
} // end of [__main]

(* ****** ****** *)

implement main () = __main () where {
  extern fun __main (): void = "__main"
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson04.dats] *)
