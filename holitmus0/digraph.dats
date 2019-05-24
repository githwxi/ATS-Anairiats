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

staload A = "funarray.dats"
staload H = "hashtable.dats"

(* ****** ****** *)

staload "digraph.sats"

(* ****** ****** *)

stadef tbl_t = $H.hashtbl_t
stadef arr_t = $A.funarray_t

typedef refbool = ref (bool)

assume node_t = string
typedef nodetbl (n:int) = $H.hashtbl_t (node_t, natLt n)

typedef matrixbool (n:int) = arr_t (arr_t (refbool, n), n)

assume digraph_t (n:int) = @{
  size= int n
, nodelst= list (node_t, n)
, nodetbl= nodetbl (n)
, matrix= matrixbool (n)
} // end of [assume]

(* ****** ****** *)

implement digraph_size (G) = G.size

implement digraph_edge_get (G, x, y) = let
  val nodetbl = G.nodetbl
  val ret = $H.hashtbl_search (nodetbl, x)
  val i_x = begin case+ ret of
    | ~Some_vt i => i
    | ~None_vt () => begin
        prerr "digraph_edge_get: not found: x = "; prerr x; exit (1)
      end // end of [None]
  end // end of [val]
  val ret = $H.hashtbl_search (nodetbl, y)
  val i_y = begin case+ ret of
    | ~Some_vt i => i
    | ~None_vt () => begin
        prerr "digraph_edge_get: not found: y = "; prerr y; exit (1)
      end // end of [None]
  end // end of [val]
in
  $A.funarray_get_elt_at ($A.funarray_get_elt_at (G.matrix, i_x), i_y)
end // end of [digraph_edge_get]

implement digraph_edge_tst (G, x, y) = begin
  let val r = digraph_edge_get (G, x, y) in !r end
end // end of [digraph_edge_tst]

implement digraph_edge_add (G, x, y) = begin
  let val r = digraph_edge_get (G, x, y) in !r := true end
end // end of [digraph_edge_add]

(* ****** ****** *)

fun matrixbool_extend {n:nat}
  (mat: matrixbool n, n: int n): matrixbool (n+1) = let
  typedef T = refbool
  typedef TS = arr_t (T, n+1)
  fun loop1 {i:nat | i <= n+1} .<n+1-i>.
    (i: int i, res: arr_t (T, i)): TS =
    if i <= n then let
      val res = $A.funarray_hiadd (res, i, ref_make_elt<bool> (false))
    in
      loop1 (i+1, res)
    end else begin
      res 
    end // end of [if]
    
  fun loop2 {i:nat | i <= n} .<n-i>.
    (i: int i, res: arr_t (TS, i)):<cloref> arr_t (TS, n) =
    if i < n then let
      val A = $A.funarray_get_elt_at (mat, i)
      val A1 = $A.funarray_hiadd (A, n, ref_make_elt<bool> (false))
    in
      loop2 (i+1, $A.funarray_hiadd (res, i, A1))
    end else begin
      res
    end // end of [if]
  val A = loop1 (0, $A.funarray_nil {T} ())
  val AA = loop2 (0, $A.funarray_nil {TS} ())
in
  $A.funarray_hiadd (AA, n, A)
end // end of [matrixbool_extend]

implement digraph_node_add {n} (G, x) = let
  val n = G.size
  val nodetbl = G.nodetbl: nodetbl (n+1)
  typedef key = node_t and itm = natLt (n+1)
  val ret = $H.hashtbl_insert_err<key,itm> (nodetbl, x, n)
  val () = case+ ret of
    | ~None_vt () => () | ~Some_vt _ => begin
        prerrf ("digraph_node_add: x = %s and n = %i", @(x, n));
        prerr_newline ()
      end // end of [Some_vt]
  val () = G.size := n+1
  val () = G.nodelst := list_cons (x, G.nodelst)
  val () = G.nodetbl := nodetbl
  val () = G.matrix := matrixbool_extend (G.matrix, n)
in
  // no return value
end // end of [digraph_node]

(* ****** ****** *)

implement fprint_digraph {m} 
  (pf | out, G) = let
  fun loop1 {n:nat}
    (out: &FILE m, G: &digraph_t n, x: string, ys: List string): void = begin
    case+ ys of
    | list_cons (y, ys) => let
        val () = if (digraph_edge_tst (G, x, y)) then begin
          fprintf (pf | out, "%s -> %s", @(x, y)); fprint_newline (pf | out)
        end
      in
        loop1 (out, G, x, ys)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [loop1]
  val nodelst = G.nodelst
  fun loop2 {n:nat}
    (out: &FILE m, G: &digraph_t n, xs: List string): void = begin
    case+ xs of
    | list_cons (x, xs) => begin
        loop1 (out, G, x, nodelst); loop2 (out, G, xs)
      end
    | list_nil () => ()
  end // end of [loop2]
in
  loop2 (out, G, nodelst)
end // end of [fprint_digraph]

implement print_digraph (x) = print_mac (fprint_digraph, x)
implement prerr_digraph (x) = prerr_mac (fprint_digraph, x)

(* ****** ****** *)

(* end of [digraph.dats] *)
