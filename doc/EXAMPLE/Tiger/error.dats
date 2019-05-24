(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "error.sats"

(* ****** ****** *)

implement abort (err) = $raise FatalError (err)

(* ****** ****** *)

(* end of [error.dats] *)
