(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

abstype symbol_t // a boxed abstract type

(* ****** ****** *)

fun symbol_name_get (x: symbol_t):<> string
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

val symbol_INT : symbol_t
val symbol_NIL : symbol_t
val symbol_STRING : symbol_t
val symbol_UNIT : symbol_t

val symbol_CHR : symbol_t
val symbol_CONCAT : symbol_t
val symbol_EXIT : symbol_t
val symbol_FLUSH : symbol_t
val symbol_GETCHAR : symbol_t
val symbol_NOT : symbol_t
val symbol_ORD : symbol_t
val symbol_PRINT : symbol_t
val symbol_PRINT_INT : symbol_t
val symbol_SIZE : symbol_t
val symbol_SUBSTRING : symbol_t

(* ****** ****** *)

abstype symtbl_t (a: t@ype) // hashtable-based implementation

fun{a:t@ype} symtbl_make (): symtbl_t (a)

fun{a:t@ype} symtbl_lookup (tbl: symtbl_t a, sym: symbol_t): Option_vt a
fun{a:t@ype} symtbl_insert (tbl: symtbl_t a, sym: symbol_t, x: a): void

(* ****** ****** *)

(* end of [symbol.sats] *)
