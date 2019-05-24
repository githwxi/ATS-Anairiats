(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload SYM = "symbol.sats"
staload ABSYN = "absyn.sats"

typedef sym = $SYM.symbol_t

(* ****** ****** *)

datatype value =
  | VALint of int
  | VALstring of string
  | VALrec of labvaluelst
  | VALarr of array0 (value)
  | VALunit of ()

and labvaluelst = 
  | LABVALUELSTcons of (sym, ref value, labvaluelst)
  | LABVALUELSTnil of ()

typedef valuelst = List value
typedef valuearr = array0 (value)

(* ****** ****** *)

fun fprint_value (out: FILEref, v: value): void

fun print_value (v: value): void
fun prerr_value (v: value): void

(* ****** ****** *)

fun interp0Prog (exp: $ABSYN.exp): value

(* ****** ****** *)

(* end of [interp0.sats] *)
