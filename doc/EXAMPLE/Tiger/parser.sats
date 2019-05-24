(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "absyn.sats"

(* ****** ****** *)

fun parse_from_stdin (): exp
fun parse_from_file (filename: string): exp

(* ****** ****** *)

(* end of [tiger_main.dats] *)
