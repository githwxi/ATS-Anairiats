(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload TL = "templab.sats"

typedef temp = $TL.temp_t
typedef label = $TL.label_t

(* ****** ****** *)

datatype exp =
  | EXPconst of int
  | EXPname of label
  | EXPtemp of temp
  | EXPbinop of (binop, exp, exp)
  | EXPmem of exp
  | EXPcall of (exp, explst)
  | EXPeseq of (stm, exp)

and stm =
  | STMmove of (exp, exp)
  | STMexp of exp
  | STMjump of (exp, List label)
  | STMcjump of (relop, exp, exp, label, label)
  | STMseq of (stm, stm)
  | STMlabel of label
  | STMusedef of  // for regalloc
      ($TL.templst(*use*), $TL.templst(*def*))
    // end of [STMusedef]

and binop =
  | PLUS | MINUS | MUL | DIV
(*
  | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR
*)

and relop = 
  | EQ | NEQ
  | GT | GE | LT | LE 
(*
  | UGT | UGE | ULT | ULE
*)

where explst = List exp and stmlst = List stm

(* ****** ****** *)

val exp_const_0 : exp // = EXPconst (0)
val exp_const_1 : exp // = EXPconst (1)

(* ****** ****** *)

val stm_nop : stm // STMexp (exp_const_0)

(* ****** ****** *)

fun fprint_exp (out: FILEref, exp: exp): void
fun print_exp (exp: exp): void
fun prerr_exp (exp: exp): void

fun fprint_stm (out: FILEref, stm: stm): void
fun print_stm (stm: stm): void
fun prerr_stm (stm: stm): void

(* ****** ****** *)

fun binop_is_additive (binop: binop): bool
fun binop_is_multiplicative (binop: binop): bool

(* ****** ****** *)

fun relop_negate (relop: relop): relop

(* ****** ****** *)

(* end of [irtree.sats] *)
