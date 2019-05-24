(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

exception FatalError of int (*errcode*)

fun abort {a:viewt@ype} (err: int): a

(* ****** ****** *)

(* end of [error.sats] *)
