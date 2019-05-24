(*
** CAS CS525, Spring 2011
** Instructor: Hongwei Xi
*)

(* ****** ****** *)

staload ABS = "absyn.sats"
typedef e0xp = $ABS.e0xp

staload SYM = "symbol.sats"
typedef sym = $SYM.symbol_t
typedef symenv (a:t@ype) = $SYM.symenv_t (a)

(* ****** ****** *)

datatype v0al =
  | V0ALbool of bool
  | V0ALint of int
  | V0ALstr of string
  | V0ALtup of List v0al 
  | V0ALclo of (env, e0xp)
  | V0ALfix of (env, e0xp)
  | V0ALref of (ref v0al)

where env = symenv (v0al)

(* ****** ****** *)

fun fprint_v0al (out: FILEref, v: v0al): void
fun fprint_v0allst (out: FILEref, vs: List (v0al)): void

fun print_v0al (v: v0al): void and prerr_v0al (v: v0al): void
overload print with print_v0al
overload prerr with prerr_v0al

(* ****** ****** *)

//
// Please implement an interpreter for the raw abstract syntax trees:
//
fun interp0_exp (e: $ABS.e0xp): v0al

(* ****** ****** *)

(* end of [interp0.sats] *)
