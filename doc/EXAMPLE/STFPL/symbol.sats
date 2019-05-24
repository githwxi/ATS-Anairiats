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

abstype symbol_t // a boxed abstract type

(* ****** ****** *)

fun symbol_get_name (x: symbol_t):<> string
fun symbol_make_name (name: string): symbol_t

(* ****** ****** *)

fun fprint_symbol (out: FILEref, x: symbol_t): void
overload fprint with fprint_symbol

fun print_symbol (x: symbol_t): void
overload print with print_symbol

fun prerr_symbol (x: symbol_t): void
overload prerr with prerr_symbol

(* ****** ****** *)

fun eq_symbol_symbol (x1: symbol_t, x2: symbol_t):<> bool
overload = with eq_symbol_symbol

fun neq_symbol_symbol (x1: symbol_t, x2: symbol_t):<> bool
overload <> with neq_symbol_symbol

fun compare_symbol_symbol (x1: symbol_t, x2: symbol_t):<> Sgn
overload compare with compare_symbol_symbol

(* ****** ****** *)

val symbol_BOOL : symbol_t // for [bool] type
val symbol_INT : symbol_t // for [int] type
val symbol_STRING : symbol_t // for [string] type
val symbol_UNIT : symbol_t // for [unit] type

(* ****** ****** *)

val symbol_PLUS : symbol_t
val symbol_MINUS : symbol_t
val symbol_TIMES : symbol_t
val symbol_SLASH : symbol_t

val symbol_UMINUS : symbol_t

val symbol_GT : symbol_t
val symbol_GTE : symbol_t
val symbol_LT : symbol_t
val symbol_LTE : symbol_t
val symbol_EQ : symbol_t
val symbol_NEQ : symbol_t

val symbol_PRINT : symbol_t
val symbol_PRINT_INT : symbol_t

(* ****** ****** *)

abstype symenv_t (a: t@ype) // hashtable-based implementation

fun{a:t@ype} symenv_make_nil (): symenv_t (a)

fun{a:t@ype}
symenv_lookup (env: symenv_t a, sym: symbol_t): Option_vt a

fun{a:t@ype}
symenv_insert (env: symenv_t a, sym: symbol_t, x: a): symenv_t a

(* ****** ****** *)

(* end of [symbol.sats] *)
