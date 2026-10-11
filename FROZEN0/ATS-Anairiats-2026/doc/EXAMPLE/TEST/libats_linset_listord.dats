(*
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May, 2011
//
*)

(* ****** ****** *)

staload LS = "libats/SATS/linset_listord.sats"
staload _(*anon*) = "libats/DATS/linset_listord.dats"

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"

(* ****** ****** *)

(*
** the efficiency gained from inlining the comparison
** function seems to be less than 5%.
*)

implement
$LS.compare_elt_elt<int> (x1, x2, _(*cmp*)) =
  if x1 < x2 then ~1 else if x1 > x2 then 1 else 0

implement main (argc, argv) = let
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = 0
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end // end of [val]
  val [n:int] n = int1_of n; val n2 = n / 2
  val () = assert (n > 0)
  val () = $RAND.srand48_with_time ()
  fn cmp (x1: int, x2: int):<cloref> Sgn = compare (x1, x2)

  var ints1: $LS.set (int) = $LS.linset_make_nil ()
  var i: int; val () =
    for (i := 0; i < n2; i := i+1) {
      val _ = $LS.linset_insert<int> (ints1, $RAND.randint n, cmp)
    } (* end of [for] *)
  // end [val]
  val size1 = $LS.linset_size (ints1)
  val () = println! ("size1 = ", size1)

  var ints2: $LS.set (int) = $LS.linset_make_nil ()
  var i: int; val () =
    for (i := n2; i < n; i := i+1) {
      val _ = $LS.linset_insert<int> (ints2, $RAND.randint n, cmp)
    } (* end of [for] *)
  // end [val]
  val size2 = $LS.linset_size (ints2)
  val () = println! ("size2 = ", size2)

  val ints_union = $LS.linset_union (ints1, ints2, cmp)
  val size = $LS.linset_size (ints_union)
  val () = println! ("size(ints_union) = ", size)
  val e_recip = 1.0 - (double_of size) / n
  val e = 1.0 / e_recip; val () = begin
    print "the constant e = "; print e; print_newline ()
  end // end of [val]
  val () = $LS.linset_free (ints_union)
//
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [libats_linset_listord.dats] *)
