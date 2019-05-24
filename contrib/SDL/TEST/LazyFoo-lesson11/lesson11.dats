//
// LazyFoo-lesson11 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson11
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: March, 2010
//

(* ****** ****** *)
//
// How to compile: see ../Makefile
//
(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"
staload "contrib/SDL/SATS/SDL_image.sats"
staload "contrib/SDL/SATS/SDL_mixer.sats"
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

(*
var music : Mix_Music // uninitialized

// Mix_Chunk: for sound effects
var scratch : Mix_Chunk // uninitalized
var high : Mix_Chunk // uninitalized
var med : Mix_Chunk // uninitalized
var low : Mix_Chunk // uninitalized
*)

(* ****** ****** *)

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val [l1:addr] (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
  val _err = TTF_Init ()
  val () = assert_errmsg (_err = 0, #LOCATION)
  val _err = Mix_OpenAudio (MIX_DEFAULT_FREQUENCY, MIX_DEFAULT_FORMAT, MIX_DEFAULT_CHANNELS, 4096)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  val () = SDL_WM_SetCaption (
    stropt_some "Monitor Music", stropt_none
  ) // end of [val]
//
  val [l2:addr] background = load_image ("LazyFoo-lesson11/background.png")
  val () = assert_errmsg (ref_isnot_null background, #LOCATION)
//
  // Open the font
  val font = TTF_OpenFont ("LazyFoo-lesson11/lazy.ttf", 30)
  val () = assert_errmsg (ref_isnot_null font, #LOCATION)
//
  val [l_music:addr] music =
    Mix_LoadMUS ("LazyFoo-lesson11/beat.wav")
  val () = assert_errmsg (Mix_Music_ref_isnot_null music, #LOCATION)
//
  val [l1:addr] scratch = Mix_LoadWAV ("LazyFoo-lesson11/scratch.wav")
  val () = assert_errmsg (Mix_Chunk_ref_isnot_null scratch, #LOCATION)
  val [l2:addr] high = Mix_LoadWAV ("LazyFoo-lesson11/high.wav")
  val () = assert_errmsg (Mix_Chunk_ref_isnot_null high, #LOCATION)
  val [l3:addr] med = Mix_LoadWAV ("LazyFoo-lesson11/medium.wav")
  val () = assert_errmsg (Mix_Chunk_ref_isnot_null med, #LOCATION)
  val [l4:addr] low = Mix_LoadWAV ("LazyFoo-lesson11/low.wav")
  val () = assert_errmsg (Mix_Chunk_ref_isnot_null low, #LOCATION)
//
  val () = apply_surface (0, 0, background, screen)
//
  var textColor : SDL_Color
//
  val () = SDL_Color_init (textColor, (Uint8)0, (Uint8)0, (Uint8)0)
  val message = TTF_RenderText_Solid (font, "Press 1, 2, 3, or 4 to play a sound effect", textColor)
  val () = assert_errmsg (ref_isnot_null message, #LOCATION)
  val w = SDL_Surface_w message
  val () = apply_surface ((SCREEN_WIDTH - w) / 2, 100, message, screen)
  val () = SDL_FreeSurface (message)
//
  val message = TTF_RenderText_Solid (font, "Press 9 to play or pause the music", textColor)
  val () = assert_errmsg (ref_isnot_null message, #LOCATION)
  val w = SDL_Surface_w message
  val () = apply_surface ((SCREEN_WIDTH - w) / 2, 200, message, screen)
  val () = SDL_FreeSurface (message)
//
  val message = TTF_RenderText_Solid (font, "Press 0 to stop the music", textColor)
  val () = assert_errmsg (ref_isnot_null message, #LOCATION)
  val w = SDL_Surface_w message
  val () = apply_surface ((SCREEN_WIDTH - w) / 2, 300, message, screen)
  val () = SDL_FreeSurface (message)
//
  val _err = SDL_Flip (screen)
  val () = assert_errmsg (_err = 0, #LOCATION)
//
  var quit: bool = false
  var event: SDL_Event?
  val () = while (~quit) let
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
        val _type = SDL_Event_type event
(*
        val () = printf ("event.type = %i\n", @((int)_type))
*)
      in
        case+ 0 of
        | _ when _type = SDL_KEYDOWN => let
            prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
            var sym = (&event)->keysym.sym
            prval () = view@ event := fpf (pf)
          in
            case+ 0 of
            | _ when sym = SDLK_1 => let
                val _err = Mix_PlayChannel(~1, scratch, 0)
              in
                assert_errmsg (_err = 0, #LOCATION)
              end // end of [SDLK_1]
            | _ when sym = SDLK_2 => let
                val _err = Mix_PlayChannel(~1, high, 0)
              in
                assert_errmsg (_err = 0, #LOCATION)
              end // end of [SDLK_2]
            | _ when sym = SDLK_3 => let
                val _err = Mix_PlayChannel(~1, med, 0)
              in
                assert_errmsg (_err = 0, #LOCATION)
              end // end of [SDLK_3]
            | _ when sym = SDLK_4 => let
                val _err = Mix_PlayChannel(~1, low, 0)
              in
                assert_errmsg (_err = 0, #LOCATION)
              end // end of [SDLK_4]
            | _ when sym = SDLK_9 => let
                val playing = Mix_PlayingMusic ()
              in
                case+ 0 of
                | _ when playing = 0 => let
                    val _err = Mix_PlayMusic (music, ~1)
                  in
                    assert_errmsg (_err = 0, #LOCATION)
                  end // end of [playing = 0]
                | _ (*playing <> 0*) => let
                    val paused = Mix_PausedMusic ()
                  in
                    case+ 0 of
                    | _ when paused = 0 => Mix_PauseMusic ()
                    | _ (*paused <> 0*) => Mix_ResumeMusic ()
                  end // end of [playing <> 0]
              end // end of [SDLK_9]
            | _ when sym = SDLK_0 => let
                val _err = Mix_HaltMusic ()
              in
                assert_errmsg (_err = 0, #LOCATION)
              end // end of [SDLK_9]
            | _ => () // ignored
          end // end of [SDL_KEYDOWN]
        | _ when _type = SDL_QUIT => quit := true
        | _ => ()
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
  in
  end // end of [val]
//
  val () = Mix_FreeMusic (music)
  val () = Mix_FreeChunk (scratch)
  val () = Mix_FreeChunk (high)
  val () = Mix_FreeChunk (med)
  val () = Mix_FreeChunk (low)
//
  val () = TTF_CloseFont (font)
  val () = SDL_FreeSurface (background)
  val () = TTF_Quit ()
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson11.dats] *)
