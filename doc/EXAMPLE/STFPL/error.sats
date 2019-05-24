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

exception Fatal of int (*errcode*)

fun abort {a:viewt@ype} (err: int):<!exn> a

(* ****** ****** *)

(* end of [error.sats] *)
