(*
//
// Author: Hongwei Xi (March, 2010)
//
*)

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload H = "libats/SATS/hashtable_chain.sats"
staload _(*anon*) = "libats/DATS/hashtable_chain.dats"

stadef HASHTBLptr = $H.HASHTBLptr

(* ****** ****** *)

// dynload "hashtable_chain.dats" // not needed as [ATS_DYNLOADFLAG = 0]

(* ****** ****** *)

(*
** the efficiency gained from inlining the comparison
** function seems to be less than 5% (more like a 3%)
*)

// (*
//
// Robert Jenkin's 32-bit function:
//
%{^
ats_int_type
__jenkin32 (ats_int_type x) {
  uint32_t a = x ;
  a = (a+0x7ed55d16) + (a<<12);
  a = (a^0xc761c23c) ^ (a>>19);
  a = (a+0x165667b1) + (a<<5);
  a = (a+0xd3a2646c) ^ (a<<9);
  a = (a+0xfd7046c5) + (a<<3);
  a = (a^0xb55a4f09) ^ (a>>16);
  return a;
} // end of [__jenkin]
%} // end of [%{^]
extern fun __jenkin32 (x: int):<> int = "__jenkin32"
implement
$H.hash_key<int> (x, _) = let
  val h = __jenkin32 (x) in ulint_of_int (h)
end // end of [hash_key]

implement $H.equal_key_key<int> (x1, x2, _) = (x1 = x2)
// *)

implement main (argc, argv) = let
  val () = gc_chunk_count_limit_max_set (~1) // infinite
  var n: int = 0
  val () = begin
    if argc >= 2 then n := int_of_string (argv.[1])
  end
  val [n:int] n = int1_of n
  val () = assert_errmsg (n > 0, #LOCATION)
(*
  val () = $RAND.srand48_with_time ()
*)
  typedef key = int and itm = string
  fn hash (x: key):<cloref> ulint = ulint_of_int (x)
  fn eq (x1: key, x2: key):<cloref> bool = (x1 = x2)

  val [l:addr] ptbl = $H.hashtbl_make {int,string} (hash, eq)
  var i: int; val () = for (i := 0; i < n; i := i+1) let
    val key = i
    // val key = $RAND.randint n
    val kstr = tostring key // val itm = sprintf ("%i", @(key))
    // val () = printf ("key = %i and itm = %s\n", @(key, itm))
  in
    $H.hashtbl_insert<key,itm> (ptbl, key, kstr)
  end // end [for]
  val size = $H.hashtbl_size (ptbl)
  val total = $H.hashtbl_total (ptbl)
  val () = begin
    print "size = "; print size; print_newline ();
    print "total = "; print total; print_newline ();
  end // end of [val]
//
  fn find {l:agz} (
      ptbl: !HASHTBLptr (key, itm, l), k0: key, res: &itm?
    ) : void = () where {
    val () = printf ("%i\t->\t", @(k0))
    val ans = $H.hashtbl_search (ptbl, k0, res)
    val () = if ans then let
      prval () = opt_unsome {itm} (res) in
      print "Some("; print res; print ")"
    end else let
      prval () = opt_unnone {itm} (res) in
      print "None()"
    end // end of [if]
    val () = print_newline ()
  } // end of [find]
//
  var res: itm?
//
  val k0 = 0
  val () = find (ptbl, k0, res)
  val k1 = 1
  val () = find (ptbl, k1, res)
  val k10 = 10
  val () = find (ptbl, k10, res)
  val k100 = 100
  val () = find (ptbl, k100, res)
  val k1000 = 1000
  val () = find (ptbl, k1000, res)
  val k10000 = 10000
  val () = find (ptbl, k10000, res)
//
  #define p2s string_of_strptr
  var !p_f = @lam
    (pf: !unit_v | k: key, i: &itm): void =<clo> i := p2s (sprintf ("%i", @(k+k+1)))
  // end of [var]
  prval pf = unit_v ()
  val () = $H.hashtbl_foreach_vclo<key,itm> {unit_v} (pf | ptbl, !p_f)
  prval unit_v () = pf
//
  val () = find (ptbl, k10000, res)
//
  var i: int; val () = for (i := 0; i < n; i := i+1) let
    val key = i
    // val key = $RAND.randint n
    val ans = $H.hashtbl_remove<key,itm> (ptbl, key, res)
    prval () = opt_clear (res)
  in
    // nothing
  end // end [for]
//
  val total = $H.hashtbl_total (ptbl)
  val () = (print "total(aft) = "; print total; print_newline ())
  val notfreed = $H.hashtbl_free_vt (ptbl)
  val () = assert_errmsg (notfreed = false, #LOCATION)
  prval () = opt_unnone (ptbl)
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [libats_hashtable_chain.dats] *)
