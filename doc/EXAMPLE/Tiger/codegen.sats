(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload AS = "assem.sats"
staload F = "frame.sats"
staload TR = "irtree.sats"

fun codegen_stm (frm: $F.frame_t, stm: $TR.stm): $AS.instrlst
fun codegen_stmlst (frm: $F.frame_t, stms: $TR.stmlst): $AS.instrlst
fun codegen_proc (frm: $F.frame_t, stms: $TR.stmlst): $AS.instrlst

(* ****** ****** *)

(* end of [codegen.sats] *)
