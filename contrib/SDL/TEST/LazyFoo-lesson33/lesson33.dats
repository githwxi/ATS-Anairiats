//
// LazyFoo-lesson33 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson33
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

//
// HX: Jan 11, 2010
// This example shows that SDL_thread is kind of buggy. I would
// stay away from using it for now.
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
      val (pf_format | p_format) = SDL_Surface_format (optimizedImage)
      val colorkey = SDL_MapRGB (!p_format, (Uint8)0, (Uint8)0xFF, (Uint8)0xFF)
      //Set all pixels of color R 0, G 0xFF, B 0xFF to be transparent
      prval () = minus_addback (pf_format | optimizedImage)
      val _err = SDL_SetColorKey (optimizedImage, SDL_SRCCOLORKEY, colorkey)
    in
      optimizedImage
    end // end of [if]
  end // end of [if]
end // end of [load_image]

(* ****** ****** *)

extern
fun apply_surface {l1,l2:anz} (
    x: int, y: int, src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2
  ) : void

implement apply_surface
  (x, y, src, dst) = () where {
  var offset: SDL_Rect // unintialized
  val () = SDL_Rect_init (offset, (Sint16)x, (Sint16)y, (Uint16)0, (Uint16)0)
  val _err = SDL_UpperBlit_ptr (src, null, dst, &offset)
} // end of [apply_surface]

(* ****** ****** *)

var quit: bool = false
val (pfbox_quit | ()) = vbox_make_view_ptr {bool} (view@ quit | &quit)
extern prfun pf_quit_get (): (bool @ quit, bool @ quit -<lin,prf> void)

fn quit_get ():<> bool = let
  prval (pf, fpf) = pf_quit_get ()
  val ans = quit
  prval () = fpf (pf)
in
  ans
end // end of [quit_get]

fn quit_set (x: bool):<> void = let
  prval (pf, fpf) = pf_quit_get ()
  val () = quit := x
  prval () = fpf (pf)
in
  // nothing
end // end of [quit_get]

extern fun myThreadFun
  (data: ptr): int = "myThreadFun"
// end of [myThreadFun]

implement myThreadFun (data) = let
  val () = while (true) let
    val () = if quit_get () then break
    val () = SDL_WM_SetCaption
      (stropt_some "Thread is running", stropt_none)
    val () = SDL_Delay((Uint32)250)
    val () = SDL_WM_SetCaption
      (stropt_some "Thread is running.", stropt_none)
    val () = SDL_Delay((Uint32)250)
    val () = SDL_WM_SetCaption
      (stropt_some "Thread is running..", stropt_none)
    val () = SDL_Delay((Uint32)250)
    val () = SDL_WM_SetCaption
      (stropt_some "Thread is running...", stropt_none)
    val () = SDL_Delay((Uint32)250)
  in
    // nothing
  end // end of [val]
in
  0 // return
end // end of [myThread]

(* ****** ****** *)

implement main () = () where {
//
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val [_l:addr] (pf_scr | screen) = SDL_SetVideoMode
    (SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE)
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
  val () = SDL_WM_SetCaption (stropt_some "Thread test", stropt_none)
//
  val [_l:addr] image = load_image ("LazyFoo-lesson33/image.png")
  val () = assert_errmsg (ref_isnot_null image, #LOCATION)
//
  val thread =
    SDL_CreateThread {ptr} (f, null) where {
    extern fun f (data: ptr):<> int = "myThreadFun"
  } // end of [val]
//
  val () = apply_surface (0, 0, image, screen)
  val _err = SDL_Flip screen
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  var event: SDL_Event?
  val () = while (true) let
    val quit = quit_get ()
(*
    val () = (print "quit = "; print quit; print_newline ())
*)
    val () = if quit then break
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
        val _type = SDL_Event_type event
        val () = (print "_type = "; print (int_of _type); print_newline ())
      in
        if _type = SDL_QUIT then quit_set (true)
      end else let
        prval () = opt_unnone (event) in break
      end // end of [if]
    end // end of [val]
  in
    // nothing
  end // end of [val]
//
  val () = SDL_KillThread (thread)
  val () = SDL_FreeSurface (image)
//
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
//
} // end of [main]

(* ****** ****** *)

(* end of [lesson33.dats] *)


