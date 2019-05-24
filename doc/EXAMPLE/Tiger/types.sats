(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "stamp.sats"
staload "symbol.sats"

(* ****** ****** *)

datatype ty =
  | TYarr of (stamp_t, ty)
  | TYbase of symbol_t
  | TYname of (symbol_t, tyref)
  | TYnil of () // TYnil <= TYrec ...
  | TYrec of (stamp_t, labtylst)
  | TYtop of () // [TYtop] should not be assigned to any expression
  | TYunit of ()
// end of [ty]

and labtylst =
  | LABTYLSTcons of (symbol_t,  ty, labtylst)
  | LABTYLSTnil of ()
// end of [labtylst]

where tylst = List ty and tyref = ref ty

(* ****** ****** *)

fun fprint_ty (out: FILEref, ty: ty): void

fun print_ty (ty: ty): void
fun prerr_ty (ty: ty): void

(* ****** ****** *)

fun ty_lnkrmv (r_ty: tyref): ty

// this one may chase links indefinitely
fun ty_normalize (ty: ty): ty

// this one may chase links at most [n] times
fun ty_normalize_max (ty: ty, n: int): ty

fun join_ty_ty (ty1: ty, ty2: ty): ty

(* ****** ****** *)

(* end of [types.sats] *)
