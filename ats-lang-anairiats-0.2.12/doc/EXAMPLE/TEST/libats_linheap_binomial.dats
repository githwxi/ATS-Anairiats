(*

// some testing code for [libats/linheap_binomial]

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2011

*)

(* ****** ****** *)
//
staload H = "libats/SATS/linheap_binomial.sats"
staload _(*anon*) = "libats/DATS/linheap_binomial.dats"
//
(* ****** ****** *)

typedef elt = int
viewtypedef heap_t = $H.heap (elt)

(* ****** ****** *)

implement
main (argc, argv) = () where {
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = 100 // default
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end // end of [va]
  val [n:int] n = int1_of_int n
  val () = assert (n > 0)
  val cmp = lam (x1: &elt, x2: &elt): Sgn =<cloref> compare_int_int (x1, x2)
  var heap: heap_t = $H.linheap_make_nil ()
  var i: Nat // uninitialized
  val () = for (i := n; i > 0; i := i-1) let
    val elt = i
    val () = $H.linheap_insert<elt> (heap, elt, cmp)
  in
    // nothing
  end // end of [val]
//
  val sz = $H.linheap_size (heap)
  val () = (print "linheap_size (heap) = "; print sz; print_newline ())
//
  val () = loop (sz, heap) where {
    val sz = size1_of_size (sz)
    fun loop {n:nat} .<n>. (
        sz: size_t n, heap: &heap_t
      ) :<cloref1> void = let
      var x: elt? // uninitialized
    in
      if sz > 0 then let
        val removed =
          $H.linheap_delmin (heap, cmp, x)
        val () = assert_errmsg (removed, #LOCATION)
        prval () = opt_unsome {elt} (x)
        // val () = (print x; print_newline ())
      in
        loop (sz-1, heap)
      end // end of [if]
    end // end of [loop]
  } // end of [loop]
//
  val sz = $H.linheap_size (heap)
  val () = (print "linheap_size (heap) = "; print sz; print_newline ())
//
  val () = $H.linheap_free<int> (heap)
//
} // end of [main]

(* ****** ****** *)

(* end of [libats_linheap_binomial.dats] *)
