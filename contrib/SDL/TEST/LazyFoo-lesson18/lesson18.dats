//
// LazyFoo-lesson18 _translated_ into ATS
// See http://lazyfoo.net/SDL_tutorials/lesson18
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"

(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"
staload "contrib/SDL/SATS/SDL_image.sats"

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
    x: int, y: int, src: !SDL_Surface_ref l1, dst: !SDL_Surface_ref l2
  ) : void

implement apply_surface
  (x, y, src, dst) = () where {
  var offset: SDL_Rect // unintialized
  val () = SDL_Rect_init (offset, (Sint16)x, (Sint16)y, (Uint16)0, (Uint16)0)
  val _err = SDL_UpperBlit_ptr (src, null, dst, &offset)
} // end of [apply_surface]

(* ****** ****** *)

#define FRAMES_PER_SECOND 20

(* ****** ****** *)

#define DOT_WIDTH 20
#define DOT_HEIGHT 20

(* ****** ****** *)

infix 0 +=; macdef += (x, d) = (,(x) := ,(x) + ,(d))
infix 0 -=; macdef -= (x, d) = (,(x) := ,(x) - ,(d))

(* ****** ****** *)

symintr int
overload int with int_of_Sint16
overload int with int_of_Uint16

(* ****** ****** *)

var theWall : SDL_Rect

local

val () = begin
  theWall.x := (Sint16)300
; theWall.y := (Sint16)40
; theWall.w := (Uint16)40
; theWall.h := (Uint16)400
end // end of [val]

in

val (pfbox_theWall | ()) =
  vbox_make_view_ptr {SDL_Rect} (view@ theWall | &theWall)
// end of [val]

end // end of [local]

(* ****** ****** *)

typedef box = @(int(*x*), int(*y*), int(*w*), int(*h*))
typedef boxlst = List box

(* ****** ****** *)

typedef Dot = @{
  boxlst= boxlst
, xulc= int, yulc= int // center coordinates
, xVel= int, yVel= int // velocity
} // end of [Dot]

(* ****** ****** *)

fn Dot_init (
    obj: &Dot? >> Dot
  , xulc: int, yulc: int, boxlst: boxlst
  ) :<> void = begin
  obj.boxlst := boxlst;
  obj.xulc := xulc; obj.yulc := yulc;
  obj.xVel := 0; obj.yVel := 0;
end // end of [Dot_init]

(* ****** ****** *)

fn Dot_handle_input
  (obj: &Dot, event: &SDL_Event): void = let
  val _type = SDL_Event_type event
in
  case+ 0 of
  | _ when _type = SDL_KEYDOWN => let
      prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
      val sym = (&event)->keysym.sym
      prval () = view@ event := fpf (pf)
    in
      case+ 0 of
      | _ when sym = SDLK_UP => obj.yVel -= 1
      | _ when sym = SDLK_DOWN => obj.yVel += 1
      | _ when sym = SDLK_LEFT => obj.xVel -= 1
      | _ when sym = SDLK_RIGHT => obj.xVel += 1
      | _ => () // ignored
    end // end of [SDL_KEYDOWN]
  | _ when _type = SDL_KEYUP => let
      prval (pf, fpf) = SDL_Event_key_castdn (view@ event)
      val sym = (&event)->keysym.sym
      prval () = view@ event := fpf (pf)
    in
      case+ 0 of
      | _ when sym = SDLK_UP => obj.yVel += 1
      | _ when sym = SDLK_DOWN => obj.yVel -= 1
      | _ when sym = SDLK_LEFT => obj.xVel += 1
      | _ when sym = SDLK_RIGHT => obj.xVel -= 1
      | _ => () // ignored
    end // end of [SDL_KEYUP]
  | _ => () // ignored
end // end of [Dot_handle_input]

(* ****** ****** *)

//
// HX: this is a terrible collison test; it is not for real
//

fn check_collision_1_1 (
    lftA: int, topA: int, rghA: int, botA: int
  , lftB: int, topB: int, rghB: int, botB: int
  ) :<> bool = begin
  case+ 0 of
  | _ when lftA >= rghB => false
  | _ when rghA <= lftB => false
  | _ when topA >= botB => false
  | _ when botA <= topB => false
  | _ => $effmask_all let
(*
      val () = (print "lftA ="; print lftA; print_newline ())
      val () = (print "rghA ="; print rghA; print_newline ())
      val () = (print "topA ="; print topA; print_newline ())
      val () = (print "botA ="; print botA; print_newline ())
      val () = (print "lftB ="; print lftB; print_newline ())
      val () = (print "rghB ="; print rghB; print_newline ())
      val () = (print "topB ="; print topB; print_newline ())
      val () = (print "botB ="; print botB; print_newline ())
*)
    in
      true
    end // end of [_]
end // end of [check_collision_1_1]

fun check_collision_1_n (
   lftA: int, rghA: int, topA: int, botA: int
 , bxs: boxlst
 ) : bool = case+ bxs of
 | list_cons (bx, bxs) =>
     if check_collision_1_1 (
       lftA, rghA, topA, botA
     , bx.0, bx.1, bx.0+bx.2, bx.1+bx.3
     ) then (
       true
     ) else check_collision_1_n (
       lftA, rghA, topA, botA, bxs
     ) // end of [if]
   // end of [list_cons]
 | list_nil () => false
// end of [check_collision_1_n]

fn check_collision_dot_n (
   obj1: &Dot, bxs2: boxlst
 ) :<> bool = $effmask_all let
 val xulc = obj1.xulc
 and yulc = obj1.yulc
 fun loop (bxs1: boxlst):<cloref1> bool = case+ bxs1 of
   | list_cons (bx1, bxs1) =>
       if check_collision_1_n (
         xulc + bx1.0, yulc + bx1.1
       , xulc + bx1.0 + bx1.2, yulc + bx1.1 + bx1.3
       , bxs2
       ) then (
         true
       ) else loop (
         bxs1
       ) // end of [if]
     // end of [list_cons]
   | list_nil () => false
in
  loop (obj1.boxlst)
end // end of [check_collision_dot_n]

(* ****** ****** *)

fn Dot_move
  (obj: &Dot, bxs: boxlst): void = () where {
  prval vbox pf_theWall = pfbox_theWall
  val xulc_old = obj.xulc
  val xulc_new = obj.xulc + obj.xVel
  val () = obj.xulc := xulc_new
  val () = (
    if xulc_new < 0 orelse
       (xulc_new + DOT_WIDTH > SCREEN_WIDTH) orelse
       check_collision_dot_n (obj, bxs)
    then begin
      obj.xulc := xulc_old
    end // end of [if]
  ) : void // end of [val]
  val yulc_old = obj.yulc
  val yulc_new = obj.yulc + obj.yVel
  val () = obj.yulc := yulc_new
  val () = (
    if yulc_new < 0 orelse
       (yulc_new + DOT_HEIGHT > SCREEN_HEIGHT) orelse
       check_collision_dot_n (obj, bxs)
    then begin
      obj.yulc := yulc_old
    end // end of [if]
  ) : void // end of [val]
} // end of [Dot_move]

(* ****** ****** *)

fn Dot_show {l1,l2:agz}
  (obj: &Dot, dot: !SDL_Surface_ref l1, screen: !SDL_Surface_ref l2): void =
  apply_surface (obj.xulc, obj.yulc, dot, screen)
// end of [Dot_show]

(* ****** ****** *)

implement main () = () where {
  val _err = SDL_Init (SDL_INIT_EVERYTHING)
  val () = assert_errmsg (_err = 0, #LOCATION)
  val [l1:addr] (pf_scr | screen) = SDL_SetVideoMode (
    SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, SDL_SWSURFACE
  ) // end of [val]
  val () = assert_errmsg (ref_isnot_null screen, #LOCATION)
  val () = SDL_WM_SetCaption (
    stropt_some "Move the dot", stropt_none
  ) // end of [val]
//
  val [l2:addr] dot = load_image ("LazyFoo-lesson18/dot.bmp")
  val () = assert_errmsg (ref_isnot_null dot, #LOCATION)
//
  var myDot: Dot // uninitialized
  var otherDot: Dot // unintialized
  val () = let
    val boxlst1: boxlst = $lst (
      @(7, 0, 6, 1)
    , @(5, 1, 10, 1)
    , @(3, 2, 14, 1)
    , @(2, 3, 16, 2)
    , @(1, 5, 18, 2)
    , @(0, 7, 20, 6)
    , @(1, 13, 18, 2)
    , @(2, 15, 16, 2)
    , @(3, 17, 14, 1)
    , @(5, 18, 10, 1)
    , @(7, 19, 6, 1)  
    ) // end of [val]
    val () = Dot_init (myDot, 0, 0, boxlst1)
    val boxlst2 = list_map_fun<box><box> (
      boxlst1, lam bx =<fun> @(bx.0 + 20, bx.1 + 20, bx.2, bx.3)
    )
    val boxlst2 = list_of_list_vt (boxlst2)
    val () = Dot_init (otherDot, 20, 20, boxlst2)
  in
    // nothing
  end // end of [val]
//
  var fps: Timer // uninitialized
  val () = Timer_init (fps)
//
  val (pf_minus, pf_fmt | p_fmt) = SDL_Surface_format (screen)
  val bg_color = SDL_MapRGB (!p_fmt, (Uint8)0xFF, (Uint8)0xFF, (Uint8)0xFF)
  prval () = minus_addback (pf_minus, pf_fmt | screen)
//
  var quit: bool = false
  var event: SDL_Event?  
//
  val () = while (~quit) let
    val () = Timer_start (fps)
    val () = while (true) begin
      if SDL_PollEvent (event) > 0 then let
        prval () = opt_unsome (event)
        val () = Dot_handle_input (myDot, event)
        val _type = SDL_Event_type event
      in
        if (_type = SDL_QUIT) then quit := true
      end else let
        prval () = opt_unnone {SDL_Event} (event) in break
      end // end of [if]
    end // end of [val]
(*
    val () = (
      print "Dot_move(bef): xulc = "; print myDot.xulc; print_newline ();
      print "Dot_move(bef): yulc = "; print myDot.yulc; print_newline ();
    ) // end of [val]
*)
    val () = Dot_move (myDot, otherDot.boxlst)
(*
    val () = (
      print "Dot_move(aft): xulc = "; print myDot.xulc; print_newline ();
      print "Dot_move(aft): yulc = "; print myDot.yulc; print_newline ();
    ) // end of [val]
*)
//
    // Fill the screen white
    val _err = SDL_FillRect_ptr (screen, null, bg_color)
//
    val () = Dot_show (myDot, dot, screen)
    val () = Dot_show (otherDot, dot, screen)
//
    val _err = SDL_Flip (screen)
    val () = assert_errmsg (_err = 0, #LOCATION)
//
    val _ticks = Timer_getTicks (fps)
    val _ratio = 1000 / FRAMES_PER_SECOND
    val _diff = _ratio - _ticks
    val () = if (_diff > 0) then SDL_Delay (Uint32(_diff))
  in
    // nothing
  end // end of [val]
//
  val () = SDL_FreeSurface (dot)
  val _ptr = SDL_Quit_Video (pf_scr | screen)
  val () = SDL_Quit ()
} // end of [main]

(* ****** ****** *)

(* end of [LazyFoo-lesson18.dats] *)
