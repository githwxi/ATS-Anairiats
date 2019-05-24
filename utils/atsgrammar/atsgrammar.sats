(*
**
** For documenting the grammar of ATS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Sylvain Nahas (sylvain.nahas AT googlemail DOT com)
**
** Time: November, 2010
**
*)

(* ****** ****** *)

macdef list_sing (x) = list_cons (,(x), list_nil)

(* ****** ****** *)

abstype tyname
abstype symbol (s:int)
abstype grmrule

(* ****** ****** *)

typedef tynamelst = List (tyname)
viewtypedef tynamelst_vt = List_vt (tyname)

fun theTynamelst_get (): tynamelst_vt
fun theTynamelst_add (x: tyname): void

(* ****** ****** *)

val theTynameNone : tyname
fun tyname_make_namdef
  (nam: string, def: string): tyname
// end of [tyname_make_namdef]

fun tyname_is_some (x: tyname): bool
fun tyname_get_nam (x: tyname): Stropt
fun tyname_get_def (x: tyname): Stropt

fun fprint_tyname (out: FILEref, x: tyname): void
fun print_tyname (x: tyname): void
fun prerr_tyname (x: tyname): void

(* ****** ****** *)

typedef symbol = [s:int] symbol (s)
typedef symlst = List (symbol)
viewtypedef symlst_vt = List_vt (symbol)

(* ****** ****** *)

datatype symreg =
  | SYMREGlit of symbol // symbol
  | SYMREGseq of (symreg, symreg) // (symreg , symreg)
  | SYMREGalt of (symreg, symreg) // (symreg | symreg)
  | SYMREGopt of (symreg) // [symreg]
  | SYMREGstar of (symreg) // {symreg}
  | SYMREGplus of (symreg) // {symreg}+
// end of [symreg]

typedef symreglst = List (symreg)

(* ****** ****** *)

typedef grmrulelst = List (grmrule)
viewtypedef grmrulelst_vt = List_vt (grmrule)

(* ****** ****** *)

fun symbol_make (name: string): symbol
fun symbol_make_nt (name: string): symbol

(* ****** ****** *)

fun eq_symbol_symbol
  (x1: symbol, x2: symbol): bool
overload = with eq_symbol_symbol

fun symbol_get_name (x: symbol): string

fun symbol_get_nonterm (x: symbol): bool
fun symbol_set_nonterm (
  x: symbol, nt: bool
) :<!ref> void = "atsgrammar_symbol_set_nonterm"
// end of [symbol_set_nonterm]

fun symbol_get_fullname (x: symbol): Stropt
fun symbol_set_fullname (
  x: symbol, fname: string
) :<!ref> void = "atsgrammar_symbol_set_fullname"
// end of [symbol_set_fullname]

fun symbol_get_tyname (x: symbol): tyname
fun symbol_set_tyname
  (x: symbol, t: tyname): void = "atsgrammar_symbol_set_tyname"
// end of [symbol_set_tyname]

fun symbol_get_grmrulelst (x: symbol): grmrulelst
fun symbol_set_grmrulelst (
  x: symbol, grs: grmrulelst
) :<!ref> void = "atsgrammar_symbol_set_grmrulelst"
// end of [symbol_set_grmrulelst]

(* ****** ****** *)

fun fprint_symbol (out: FILEref, sym: symbol): void

fun print_symbol (sym: symbol): void
overload print with print_symbol
fun prerr_symbol (sym: symbol): void
overload prerr with prerr_symbol

(* ****** ****** *)

fun grmrule_make_symlst (xs: symlst): grmrule
fun grmrule_make_symreglst (knd: int, xs: symreglst): grmrule

(* ****** ****** *)

fun grmrule_get_kind (gr: grmrule): int
(*
fun grmrule_set_kind
  (gr: grmrule, knd: int): void = "atsgrammar_grmrule_set_kind"
// end of [grmrule_set_kind]
*)

fun grmrule_get_merged (gr: grmrule): int
fun grmrule_set_merged
  (gr: grmrule, merged: int): void = "atsgrammar_grmrule_set_merged"
// end of [grmrule_set_merged]

fun grmrule_get_action (gr: grmrule): Stropt
fun grmrule_set_action
  (gr: grmrule, action: string): void = "atsgrammar_grmrule_set_action"
// end of [grmrule_set_action]

fun grmrule_get_precval (gr: grmrule): Stropt
fun grmrule_set_precval
  (gr: grmrule, precval: string): void = "atsgrammar_grmrule_set_precval"
// end of [grmrule_set_precval]

fun grmrule_get_symreglst (gr: grmrule): symreglst

(* ****** ****** *)

fun theSymbolStampCount_getinc (): int
fun theSymlst_get (): symlst_vt
fun theSymlst_add (x: symbol): void

(* ****** ****** *)

fun theGrmrulelst_get (): grmrulelst_vt
fun theGrmrulelst_add (x: grmrule): void

fun theGrmrulelst_merge_all (x: symbol, r: symreg): void

(* ****** ****** *)
//
absview symbol_open_v (s:int)
//
fun symbol_open {s:int}
  (sym: symbol (s)): (symbol_open_v (s) | void)
// end of [symbol_open]
//
fun symbol_close {s:int}
  (pf: symbol_open_v (s) | sym: symbol (s)): void
// end of [symbol_clsoe]
//
(* ****** ****** *)

symintr grmrule_append
//
fun grmrule_append_empty (): grmrule
overload grmrule_append with grmrule_append_empty
//
fun grmrule_append_symbol (x: symbol): grmrule
overload grmrule_append with grmrule_append_symbol
//
fun grmrule_append_symlst (xs: symlst): grmrule
overload grmrule_append with grmrule_append_symlst
//
fun grmrule_append_grmrule (gr: grmrule): grmrule
overload grmrule_append with grmrule_append_grmrule
//
(* ****** ****** *)

fun emit_yats (out: FILEref): void
fun emit_yats_html (out: FILEref): void

fun emit_desc (out: FILEref): void
fun emit_desc_html (out: FILEref): void

(* ****** ****** *)

(* end of [atsgrammar.sats] *)
