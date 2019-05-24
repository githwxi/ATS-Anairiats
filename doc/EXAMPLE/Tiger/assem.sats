(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

local

staload TL = "templab.sats"

typedef temp = $TL.temp_t
typedef templst = List temp
typedef label = $TL.label_t
typedef lablst = List label
typedef lablstopt = Option (lablst)

in // in of [local]

datatype instr =
  | INSTRoper of (
      string(*asm*)
    , templst(*src*)
    , templst(*dst*)
    , lablstopt(*jump*)
    ) // end of [INSTRoper]
  | INSTRlabel of (string(*asm*), label)
  | INSTRmove of (
      string(*asm*), temp(*src*), temp(*dst*)
    ) // end of [INSTRmove]

typedef instrlst = List instr
viewtypedef instrlst_vt = List_vt (instr)
typedef instropt = Option instr
viewtypedef instropt_vt = Option_vt (instr)

fun fprint_instr (out: FILEref, ins: instr): void
fun print_instr (ins: instr): void
fun prerr_instr (ins: instr): void

fun fprint_instrlst (out: FILEref, inss: instrlst): void
fun print_instrlst (inss: instrlst): void
fun prerr_instrlst (inss: instrlst): void

// Instead of turning an instruction into a string and then print it out,
// it should make a lot more sense to print out the instruction directly,
// right?
fun instr_format (fmt: temp -<fun1> string, ins: instr): string

fun instr_ismove (ins: instr): bool

fun instr_uselst_get (ins: instr): templst

fun instr_deflst_get (ins: instr): templst

fun instr_jump_get (ins: instr): Option (lablst)

end // end of [local]

(* ****** ****** *)

(* end of [assem.sats] *)
