(*
** Course: Concepts of Programming Languages (BU CAS CS 320)
** Semester: Summer I, 2009
** Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2009
//

(* ****** ****** *)

staload "error.sats"

(* ****** ****** *)

implement abort (err: int) = $raise Fatal (err)

(* ****** ****** *)

(* end of [error.dats] *)
