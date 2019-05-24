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

staload AS = "assem.sats"

(* ****** ****** *)

abstype frame_t

abstype access_t
typedef accesslst = List access_t

fun access_is_inreg (acc: access_t): bool // allocated in a reg
fun access_is_inframe (acc: access_t): bool // allocated in the frame

(* ****** ****** *)

val RV : temp // return value
val FP : temp // frame pointer
val SP : temp // stack pointer

(* ****** ****** *)

// [WORDSIZE} is the number of bytes in a pointer
val WORDSIZE : int // it is defined in [params.hats]

(* ****** ****** *)

val theTopFrame : frame_t

// The stack pointer may be pushed further after args are loaded
// [argofs] tells the difference between SP and the 1st argument
fun frame_make_new
  (lab: label, argofs: int, arglst: List bool(*escape status*)): frame_t

fun frame_name_get (f: frame_t): label
fun frame_argofs_get (f: frame_t): int
fun frame_arglst_get (f: frame_t): accesslst

fun frame_size_get (f: frame_t): int
fun frame_alloc_local (f: frame_t, isEscaped: bool): access_t

(* ****** ****** *)

staload TREE = "irtree.sats"

val exp_FP : $TREE.exp
val exp_SP : $TREE.exp
val exp_RV : $TREE.exp

fun exp_make_access (e_off: $TREE.exp, acc: access_t): $TREE.exp

datatype frag =
  | FRAGproc of (frame_t, $TREE.stm) | FRAGstring of (label, string)
// end of [frag]

typedef fraglst = List frag
viewtypedef fraglst_vt = List_vt frag

fun frame_theFraglst_get (): fraglst
fun frame_theFraglst_add (frag: frag): void
fun frame_theFraglst_reset (): void

(* ****** ****** *)

abstype reg_t (* string *)

fun temp_reg_find (tmp: temp): Option (reg_t)

val theFunargReglst : List temp //
// registers for passing function arguments

val theSpecialReglst : List temp //
// registers for some special purposes (e.g., SP, FP)

val theGeneralReglst : List temp // for general purpose

val theCallersavedReglst : List temp // caller saved registers
val theCalleesavedReglst : List temp // callee saved registers

(* ****** ****** *)

// viewshifting and saving/restoring calleesaved registers have
// been merged into [translate.dats]
fun procEntryExit1_entr (frm: frame_t, inss: &($AS.instrlst_vt)): void
fun procEntryExit1_exit (frm: frame_t, inss: &($AS.instrlst_vt)): void

fun procEntryExit1_entr_emit (out: FILEref, frm: frame_t): void

// adding a "sink" instruction
fun procEntryExit2 (frm: frame_t, inss: &($AS.instrlst_vt)): void

(* ****** ****** *)

//
// for generating instructions to be inserted after actuall spilling happens
// during register allocation
//
fun instr_make_mem_read (acc: access_t, tmp: $TL.temp_t): $AS.instr
fun instr_make_mem_write (acc: access_t, tmp: $TL.temp_t): $AS.instr

(* ****** ****** *)

// return the name of a machine register
fun register_name_get (tmp: $TL.temp_t): string

(* ****** ****** *)

#include "params.hats"

#if MARCH = "SPIM" #then

val ZERO : temp (* r0 *)

val RA : temp (* the return value register // r31 *)
val exp_RA: $TREE.exp

#endif

(* ****** ****** *)

#if MARCH = "x86_32" #then

val EAX : temp
val EBX : temp
val ECX : temp
val EDX : temp

val ESI : temp
val EDI : temp

val ESP : temp
val EBP : temp

#endif

(* ****** ****** *)

(* end of [frame.sats] *)
