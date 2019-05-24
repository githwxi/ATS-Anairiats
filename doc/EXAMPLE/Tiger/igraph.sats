(*
**
** TIGERATS: a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

// interfere graph for liveness analysis

(* ****** ****** *)

staload AS = "assem.sats"
staload TL = "templab.sats"

(* ****** ****** *)

staload "tempset.sats"

(* ****** ****** *)

staload "fgraph.sats"

(* ****** ****** *)

abstype ignodeinfo_t // information stored at each node

(* ****** ****** *)

fun ignodeinfo_ismov (info: ignodeinfo_t):<> bool

(* ****** ****** *)

fun ignodeinfo_intset_get
  (info: ignodeinfo_t):<> tempset_t
// end of [ignodeinfo_intset_get]

fun ignodeinfo_intset_set
  (info: ignodeinfo_t, intset: tempset_t):<!ref> void
  = "ignodeinfo_intset_set"
// end of [ignodeinfo_intset_set]

fun ignodeinfo_movset_get
  (info: ignodeinfo_t):<> tempset_t
// end of [ignodeinfo_movset_get]

fun ignodeinfo_movset_set
  (info: ignodeinfo_t, movset: tempset_t):<!ref> void
  = "ignodeinfo_movset_set"
// end of [ignodeinfo_movset_set]

fun ignodeinfo_nlivtot_get (info: ignodeinfo_t):<> int
fun ignodeinfo_nlivtot_set (info: ignodeinfo_t, n: int):<!ref> void
  = "ignodeinfo_nlivtot_set"
fun ignodeinfo_nlivtot_inc (info: ignodeinfo_t):<!ref> void
  = "ignodeinfo_nlivtot_inc"

fun ignodeinfo_nusedef_get (info: ignodeinfo_t):<> int
fun ignodeinfo_nusedef_set (info: ignodeinfo_t, n: int):<!ref> void
  = "ignodeinfo_nusedef_set"
fun ignodeinfo_nusedef_inc (info: ignodeinfo_t):<!ref> void
  = "ignodeinfo_nusedef_inc"

(* ****** ****** *)

fun ignodeinfo_make (tmp: $TL.temp_t):<> ignodeinfo_t

(* ****** ****** *)

fun fprint_ignodeinfo (out: FILEref, info: ignodeinfo_t): void

fun print_ignodeinfo (info: ignodeinfo_t): void
fun prerr_ignodeinfo (info: ignodeinfo_t): void

(* ****** ****** *)

abstype igraph_t

(* ****** ****** *)

fun igraph_make_empty (): igraph_t

(* ****** ****** *)

fun fprint_igraph (out: FILEref, ig: igraph_t): void

(* ****** ****** *)

fun igraph_initialize (ig: igraph_t): void

(* ****** ****** *)

fun igraph_nodeinfo_get
  (ig: igraph_t, t: $TL.temp_t): ignodeinfo_t
// end of [igraph_nodeinfo_get]

fun igraph_nodeinfo_set
  (ig: igraph_t, t: $TL.temp_t, info: ignodeinfo_t): void
// end of [igraph_nodeinfo_set]

(* ****** ****** *)

// adding an interference edge
fun igraph_int_edge_insert
  (ig: igraph_t, tmp1: $TL.temp_t, tmp2: $TL.temp_t): void
// end of [igraph_int_edge_insert]

// removing an interference edge
fun igraph_int_edge_remove
  (ig: igraph_t, tmp1: $TL.temp_t, tmp2: $TL.temp_t): void
// end of [igraph_int_edge_remove]

(* ****** ****** *)

// adding a move edge
fun igraph_mov_edge_insert
  (ig: igraph_t, tmp1: $TL.temp_t, tmp2: $TL.temp_t): void
// end of [igraph_mov_edge_insert]

// removing a move edge
fun igraph_mov_edge_remove
  (ig: igraph_t, tmp1: $TL.temp_t, tmp2: $TL.temp_t): void
// end of [igraph_mov_edge_remove]

(* ****** ****** *)

// inserting a node
fun igraph_node_insert
  (ig: igraph_t, tmp: $TL.temp_t): void
// end of [[igraph_node_insert]

// removing a node and all the edges involving this node
fun igraph_node_remove
  (ig: igraph_t, tmp: $TL.temp_t): void
// end of [igraph_node_remove]

// merging [tmp0] and [tmp1]
fun igraph_node_coalesce
  (ig: igraph_t, tmp0: $TL.temp_t, tmp1: $TL.temp_t): void
// end of [igraph_node_coalesce]

// freezing [tmp]
fun igraph_node_freeze
  (ig: igraph_t, tmp: $TL.temp_t): void
// end of [igraph_node_freeze]

(* ****** ****** *)

fun igraph_make_fgraph (fg: fgraph_t): igraph_t

fun spillcost_compute (fg: fgraph_t, ig: igraph_t): void

fun igraph_make_instrlst (inss: $AS.instrlst): igraph_t

(* ****** ****** *)

fun igraph_search_lowdeg
  (ig: igraph_t): Option_vt ($TL.temp_t)
// end of [igraph_search_lowdeg]

fun igraph_search_coalesce
  (ig: igraph_t): Option_vt @($TL.temp_t, $TL.temp_t)
// end of [igraph_search_coalesce]

fun igraph_search_freeze
  (ig: igraph_t): Option_vt ($TL.temp_t)
// end of [igraph_search_freeze]

fun igraph_search_spill
  (ig: igraph_t): Option_vt ($TL.temp_t)
// end of [igraph_search_spill]

(* ****** ****** *)

(* end of [igraph.sats] *)
