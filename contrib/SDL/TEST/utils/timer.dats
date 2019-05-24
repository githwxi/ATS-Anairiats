//
// A simple timer
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: January, 2010
//

(* ****** ****** *)

staload "contrib/SDL/SATS/SDL.sats"

(* ****** ****** *)

staload "timer.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynamic loading

(* ****** ****** *)

//
// HX: Okay, let us do some object-oriented programming in ATS :)
//

(* ****** ****** *)

assume Timer_private =
  $extype_struct "Timer" of {
  startTicks= int
, started= bool
, pausedTicks= int
, paused= bool
} // end of [Timer_private]

(* ****** ****** *)

macdef _GetTicks () = int_of_Uint32 (SDL_GetTicks ())

(* ****** ****** *)

implement
Timer_init (obj) = begin
  obj.private.startTicks := 0 ;
  obj.private.pausedTicks := 0 ;
  obj.private.paused := false ;
  obj.private.started := false ;
end // end of [Timer_init]

implement
Timer_start (obj) = begin
  obj.private.started := true ; obj.private.paused := false ;
  obj.private.startTicks := _GetTicks ()
end // end of [Timer_start]

implement
Timer_stop (obj) = begin
  obj.private.started := false ; obj.private.paused := false ;
end // end of [Timer_stop]

implement
Timer_pause (obj) =
  if (obj.private.started) then
    if ~(obj.private.paused) then begin
      obj.private.paused := true;
      obj.private.pausedTicks := _GetTicks () - obj.private.startTicks
    end // end of [if]
  // end of [if]
// end of [Timer_pause]

implement
Timer_unpause (obj) =
  if (obj.private.paused) then begin
    obj.private.paused := false ;
    obj.private.startTicks := _GetTicks () - obj.private.pausedTicks ;
    obj.private.pausedTicks := 0
  end // end of [if]
// end of [Timer_unpause]

implement
Timer_getTicks (obj) =
(
if (obj.private.started)
  then
    if (obj.private.paused)
      then obj.private.pausedTicks else _GetTicks() - obj.private.startTicks
    // end of [if]
  else (0) // end of [if]
// end of [if]
) (* end of [Timer_getTicks] *)

implement Timer_is_paused (obj) = obj.private.paused
implement Timer_is_started (obj) = obj.private.started

(* ****** ****** *)

(* end of [timer.dats] *)
