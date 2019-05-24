(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "symbol.sats"
staload "types.sats"
staload "absyn.sats"

(* ****** ****** *)

datatype vfty_node =
  VFTYvar of (refb(*escape*), ty) | VFTYfun of (tylst, ty)

typedef vfty = '{
  vfty_level= int, vfty_node= vfty_node
} // end of [vfty]

(* ****** ****** *)

fun vfty_var_make (level: int, r: refb, ty: ty): vfty
fun vfty_fun_make (level: int, _arg: tylst, _res: ty): vfty

(* ****** ****** *)

fun transProg (e: exp): ty // the main typechecking function

(* ****** ****** *)

(* end of [tychecker.sats] *)
