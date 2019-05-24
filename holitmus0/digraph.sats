(*
**
** HOLITMUS: a proof checker for higher-order logic
**
** Originally implemented in OCaml
**    by Chad Brown (cebrown AT mathgate DOT info)
** Time: March/September, 2008
**
** Translated to ATS
**    by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: November, 2008
**
*)

(* ****** ****** *)

abstype node_t
abst@ype digraph_t (int)
typedef digraph_t = [n:nat] digraph_t (n)

(* ****** ****** *)

fun digraph_nil {n:nat} (): [l:addr] @(digraph_t 0 @ l | ptr l)

typedef boolref = ref bool

fun digraph_size {n:nat} (G: &digraph_t n): int n
fun digraph_edge_get {n:nat}
  (G: &digraph_t n, x: node_t, y: node_t): boolref 

// test if an edge exists between two given nodes
fun digraph_edge_tst {n:nat}
  (G: &digraph_t n, x: node_t, y: node_t): bool

// add an edge between two given nodes
fun digraph_edge_add {n:nat}
  (G: &digraph_t n, x: node_t, y: node_t): void

// add a node
fun digraph_node_add {n:nat}
  (G: &digraph_t n >> digraph_t (n+1), x: node_t): void

(* ****** ****** *)

fun fprint_digraph {m:file_mode} {n:nat}
  (pf: file_mode_lte (m, w) | out: &FILE m, G: &digraph_t n): void

fun print_digraph {n:nat} (G: &digraph_t n): void
fun prerr_digraph {n:nat} (G: &digraph_t n): void

(* ****** ****** *)

(* end of [digraph.sats] *)
