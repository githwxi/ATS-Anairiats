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
staload TR = "irtree.sats"

(* ****** ****** *)

(*
** From an arbitrary Tree statement, produce a list of cleaned trees
** satisfying the following properties:
** 1.  No SEQ's or ESEQ's
** 2.  The parent of every CALL is STMmove(TEMP t,..)
*)

fun linearize (stm: $TR.stm): $TR.stmlst

typedef block = '{
  block_lab= $TL.label_t
, block_init= $TR.stmlst
, block_last= $TR.stm
} // end of [block]

typedef blocklst = List block

(*
** From a list of cleaned trees, produce a list of basic blocks
** satisfying the following properties:
** 1. and 2. as above;
** 3.  Every block begins with a LABEL;
** 4.  A LABEL appears only at the beginning of a block;
** 5.  Any JUMP or CJUMP is the last stm in a block;
** 6.  Every block ends with a JUMP or CJUMP;
** Also produce the "label" to which control will be passed upon exit.
*)

fun blocklst_gen (stms: $TR.stmlst): @($TL.label_t, blocklst)

(*
** From a list of basic blocks satisfying properties 1-6, along with
** an "exit" label, produce a list of stms such that:
** 1. and 2. as above;
** 7. Every CJUMP(_,t,f) is immediately followed by LABEL f.
** The blocks are reordered to satisfy property 7; in this reordering
** as many JUMP(NAME(lab)) statements as possible are eliminated by
** falling through into LABEL(lab).
*)

fun trace_schedule (lab: $TL.label_t, blks: blocklst): $TR.stmlst

(* ****** ****** *)

(* end of [canonical.sats] *)
