(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

// control flow graph for liveness analysis

(* ****** ****** *)

staload AS = "assem.sats"
staload TL = "templab.sats"

(* ****** ****** *)

staload "tempset.sats"

(* ****** ****** *)

staload "fgnode.sats"

(* ****** ****** *)

abstype fgnodeinfo_t // information stored at each node

(* ****** ****** *)

fun fgnodeinfo_ismove_get (info: fgnodeinfo_t): bool

fun fgnodeinfo_pred_get (info: fgnodeinfo_t): fgnodelst_t
fun fgnodeinfo_succ_get (info: fgnodeinfo_t): fgnodelst_t

fun fgnodeinfo_useset_get (info: fgnodeinfo_t): tempset_t
fun fgnodeinfo_defset_get (info: fgnodeinfo_t): tempset_t
fun fgnodeinfo_inset_get (info: fgnodeinfo_t): tempset_t
fun fgnodeinfo_outset_get (info: fgnodeinfo_t): tempset_t

(* ****** ****** *)

fun fgnodeinfo_pred_set
  (info: fgnodeinfo_t, fgns: fgnodelst_t): void
  = "fgnodeinfo_pred_set"

fun fgnodeinfo_succ_set
  (info: fgnodeinfo_t, fgns: fgnodelst_t): void
  = "fgnodeinfo_succ_set"

fun fgnodeinfo_inset_set
  (info: fgnodeinfo_t, ts: tempset_t): void
  = "fgnodeinfo_inset_set"

fun fgnodeinfo_outset_set
  (info: fgnodeinfo_t, ts: tempset_t): void
  = "fgnodeinfo_outset_set"

(* ****** ****** *)

fun fgnodeinfo_make (
    fgn: fgnode_t
  , ismove: bool, uselst: $TL.templst, deflst: $TL.templst
  ) :<> fgnodeinfo_t
// end of [fgnodeinfo_make]

(* ****** ****** *)

fun fprint_fgnodeinfo (out: FILEref, info: fgnodeinfo_t): void

fun print_fgnodeinfo (info: fgnodeinfo_t): void
fun prerr_fgnodeinfo (info: fgnodeinfo_t): void

(* ****** ****** *)

abstype fgraph_t

(* ****** ****** *)

fun fprint_fgraph (out: FILEref, fg: fgraph_t): void

(* ****** ****** *)

fun fgraph_make_elt {n:nat} (n: int n, info: fgnodeinfo_t): fgraph_t

(* ****** ****** *)

fun fgraph_size (fg: fgraph_t): size_t

(* ****** ****** *)

fun fgraph_nodeinfo_get (fg: fgraph_t, n: fgnode_t): fgnodeinfo_t
fun fgraph_nodeinfo_set (fg: fgraph_t, n: fgnode_t, info: fgnodeinfo_t): void

(* ****** ****** *)

fun fgraph_edge_insert (fg: fgraph_t, fr: fgnode_t, to: fgnode_t): void

(* ****** ****** *)

fun fgraph_make_instrlst (inss: $AS.instrlst): fgraph_t
fun fgraph_compute_outset (fg: fgraph_t): void

(* ****** ****** *)

(* end of [fgraph.sats] *)
