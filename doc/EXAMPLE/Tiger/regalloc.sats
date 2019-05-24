(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload AS = "assem.sats"
staload TL = "templab.sats"

(* ****** ****** *)

staload F = "frame.sats"

(* ****** ****** *)

staload "tempset.sats"

staload "fgraph.sats"

staload "igraph.sats"

(* ****** ****** *)

//
// remove those registers that cannot be used
// for general purpose (e.g., SP and FP)
//
fun igraph_simplify0 (ig: igraph_t): void

(* ****** ****** *)

datatype regassgn =
  | REGASSGNsimplify of ($TL.temp_t, tempset_t)
  | REGASSGNcoalesce of ($TL.temp_t, $TL.temp_t)
  | REGASSGNspill of ($TL.temp_t, tempset_t)

typedef regassgnlst = List regassgn

fun fprint_regassgn (out: FILEref, rasgn: regassgn): void

fun fprint_regassgnlst (out: FILEref, rasgns: regassgnlst): void

(* ****** ****** *)

fun regassgn_select (rasgn: regassgn): void

(* ****** ****** *)

fun regassgn_find (tmp: $TL.temp_t): $TL.temp_t

(* ****** ****** *)

fun regalloc_tmpfmt (tmp: $TL.temp_t): string
fun regalloc_insfmt (ins: $AS.instr): string

fun instrlst_regalloc (frm: $F.frame_t, inss: $AS.instrlst): $AS.instrlst

(* ****** ****** *)

(* end of [regalloc.sats] *)
