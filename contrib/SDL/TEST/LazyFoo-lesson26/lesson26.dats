//
// LazyFoo-lesson26 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson26
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

viewtypedef Window (l:addr) = @{
  windowed= bool
, windowOK= bool
, pfscr= Video_v l
, screen= SDL_Surface_ref l
}

viewtypedef Window = [l:addr] Window l

extern
fun Window_handle_events
  (obj: &Window, event: &SDL_Event): void

extern
fun Window_toggle_fullscreen (obj: &Window): void

extern
fun Window_error (obj: &Window): bool

(* ****** ****** *)

overload int_of with int_of_Uint8
overload uint_of with uint_of_Uint8

implement Window_handle_events
  (obj, event) = case+ 0 of
  | _ when obj.windowOK => let
      val _type = SDL_Event_type event
    in
      case+ 0 of
      | _ when _type = SDL_VIDEORESIZE => () where {
          prval (pf, fpf) = SDL_Event_resize_castdn (view@ event)
          val w = (&event)->w and h = (&event)->h
          prval () = view@ event := fpf (pf)
          val (pfscr | screen) = SDL_ResetVideoMode (
            obj.pfscr
          | obj.screen
          , w, h, SCREEN_BPP, SDL_SWSURFACE lor SDL_RESIZABLE
          )
          prval () = obj.pfscr := pfscr
          val () = obj.screen := screen
          val () = if ref_is_null obj.screen then (obj.windowOK := false)
        } // end of [SDL_VIDEORESIZE]
      | _ when _type = SDL_KEYDOWN => let
          prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
          val sym = (&event)->keysym.sym
          prval () = view@ event := fpf (pf)
        in
          if sym = SDLK_RETURN then Window_toggle_fullscreen (obj)
        end // end of [_ when ...]
      
            //If the window focus changed
      | _ when _type = SDL_ACTIVEEVENT => let
          prval (pf, fpf) = SDL_Event_active_castdn (view@ event)
          val state = (&event)->state
          prval () = view@ event := fpf (pf)
        in
          case+ 0 of
          | _ when uint_of (state land SDL_APPACTIVE) > 0U => let
              prval (pf, fpf) = SDL_Event_active_castdn (view@ event)
              val gain = (&event)->gain
              prval () = view@ event := fpf (pf)
            in
              if (int_of)gain = 0 then SDL_WM_SetCaption
                (stropt_some "Window Event Test: Iconified", stropt_none)
              else SDL_WM_SetCaption
                (stropt_some "Window Event Test", stropt_none)
              // end of [if]
            end // end of [_ when ...]
          | _ when uint_of (state land SDL_APPINPUTFOCUS) > 0U => let
              prval (pf, fpf) = SDL_Event_active_castdn (view@ event)
              val gain = (&event)->gain
              prval () = view@ event := fpf (pf)
            in
              if (int_of)gain = 0 then SDL_WM_SetCaption
                (stropt_some "Window Event Test: Keyboard focus lost", stropt_none)
              else SDL_WM_SetCaption
                (stropt_some "Window Event Test", stropt_none)
              // end of [if]
            end // end of [_ when ...]
          | _ when uint_of (state land SDL_APPMOUSEFOCUS) > 0U => let
              prval (pf, fpf) = SDL_Event_active_castdn (view@ event)
              val gain = (&event)->gain
              prval () = view@ event := fpf (pf)
            in
              if (int_of)gain = 0 then SDL_WM_SetCaption
                (stropt_some "Window Event Test: Mouse focus lost", stropt_none)
              else SDL_WM_SetCaption
                (stropt_some "Window Event Test", stropt_none)
              // end of [if]
            end // end of [_ when ...]
          | _ => ()
        end // end of [SDL_ACTIVEEVENT]
      | _ when _type = SDL_VIDEOEXPOSE => let
          val () = assert_errmsg (ref_isnot_null obj.screen, #LOCATION)
          val _err = SDL_Flip (obj.screen)
        in
          if (_err < 0) then obj.windowOK := false
        end // end of [_ when ...]
      | _ => () // ignored
    end // end of [obj.windowOK = true]
  | _ => () // obj.windowOK = false
// end of [Window_handle_events]

implement Window_toggle_fullscreen (obj) = case+ 0 of
  | _ when obj.windowed => let
      val (pfscr | screen ) = SDL_ResetVideoMode (
        obj.pfscr
      | obj.screen
      , SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP
      , SDL_SWSURFACE lor SDL_RESIZABLE lor SDL_FULLSCREEN
      )
      prval () = obj.pfscr := pfscr
      val () = obj.screen := screen
    in
      if ref_is_null obj.screen then
        obj.windowOK := false
      else
        obj.windowed := false
      // end of [if]
    end // end of [val]
  | _ (*fullscreen*) => let
      val (pfscr | screen ) = SDL_ResetVideoMode (
        obj.pfscr
      | obj.screen
      , SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP
      , SDL_SWSURFACE lor SDL_RESIZABLE
      )
      prval () = obj.pfscr := pfscr
      val () = obj.screen := screen
    in
      if ref_is_null obj.screen then
        obj.windowOK := false
      else
        obj.windowed := true
      // end of [if]
    end // end of [_]
// end of [Window_toggle_fullscreen]

implement Window_error (obj) = ~(obj.windowOK)

(* ****** ****** *)

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val [l1:addr] (pfscr | screen) = SDL_SetVideoMode
    (SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE lor SDL_RESIZABLE)
  // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
//
  val [l2:addr] testing = load_image ("LazyFoo-lesson26/window.png")
  val () = assert_errmsg (ref_isnot_null testing, #LOCATION)
//
  var myWin: Window null
  val () = myWin.windowOK := true
  val () = myWin.windowed := true
  prval () = myWin.pfscr := pfscr
  val () = myWin.screen := screen
  val () = SDL_WM_SetCaption (stropt_some "Window Event Test", stropt_none)
//
  var quit: bool = false
  var event: SDL_Event? // uninitialized
  val () = while*
    (myWin: Window) => (~quit) let
    val () = while*
      (myWin: Window) => (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
        val () = Window_handle_events (myWin, event)
        val _type = SDL_Event_type event
(*
        val () = printf ("event.type = %i\n", @((int)_type))
*)
        val () = case+ 0 of
          | _ when _type = SDL_QUIT => quit := true
          | _ when _type = SDL_KEYDOWN => let
              prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
              val sym = (&event)->keysym.sym
              prval () = view@ event := fpf (pf)
            in
              if sym = SDLK_ESCAPE then quit := true
            end // end of [_ when ...]
          | _ => () // ignored
        // end of [val]
      in
        continue
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
    val () = if Window_error (myWin) then exit (1)
    val () = assert_errmsg (ref_isnot_null myWin.screen, #LOCATION)
//
    val (pf_minus, pf_fmt | p_fmt) = SDL_Surface_format (myWin.screen)
    val color = SDL_MapRGB (!p_fmt, (Uint8)0xFF, (Uint8)0xFF, (Uint8)0xFF)
    prval () = minus_addback (pf_minus, pf_fmt | myWin.screen)
//
    val _err = SDL_FillRect_ptr (myWin.screen, null, color)
    val () = assert_errmsg (_err = 0, #LOCATION)
    val () = apply_surface
      ((w1 - w2) / 2, (h1 - h2) / 2, testing, myWin.screen) where {
      val w1 = SDL_Surface_w (myWin.screen)
      val w2 = SDL_Surface_w (testing)
      val h1 = SDL_Surface_h (myWin.screen)
      val h2 = SDL_Surface_h (testing)
    } // end of [val]
    val _err = SDL_Flip (myWin.screen)
    val () = assert_errmsg (_err = 0, #LOCATION)
//
  in
    // nothing
  end // end of [val]
//
  val () = SDL_FreeSurface (testing)
  val _ptr = SDL_Quit_Video (myWin.pfscr | myWin.screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson26.dats] *)
