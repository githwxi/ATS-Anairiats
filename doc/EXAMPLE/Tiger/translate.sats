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

staload TL = "templab.sats"
staload TR = "irtree.sats"

(* ****** ****** *)

datatype e1xp =
  | Ex of $TR.exp
  | Nx of $TR.stm
  | Cx of ($TL.label_t, $TL.label_t) -<cloref1> $TR.stm

fun unEx (e1xp: e1xp): $TR.exp
fun unNx (e1xp: e1xp): $TR.stm
fun unCx (e1xp: e1xp): ($TL.label_t, $TL.label_t) -<cloref1> $TR.stm

(* ****** ****** *)

fun fprint_e1xp (out: FILEref, e1xp: e1xp): void
fun print_e1xp (e1xp: e1xp): void
fun prerr_e1xp (e1xp: e1xp): void

(* ****** ****** *)

fun transProg1 (exp: exp): e1xp

(* ****** ****** *)

(* end of [translate.dats] *)
