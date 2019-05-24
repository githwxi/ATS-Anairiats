//
//
// code for illustration in references.html
//
//

(* ****** ****** *)

staload "prelude/DATS/pointer.dats"
staload "prelude/DATS/reference.dats"

(* ****** ****** *)

val r_int = ref_make_elt<int> (0)
val r_double = ref_make_elt<double> (0.0)
val r_fun = ref_make_elt<int->int> (lam x => x+1)

(*

fun vbox_make_view_ptr {a:viewt@ype}
  {l:addr} (pf_at: a @ l | ptr l): (vbox (a @ l) | void)

*)

fn{a:viewt@ype}
ref_make_elt (x: a): ref a = let
  val (pf_gc, pf_at | p) = ptr_alloc<a> ()
  prval () = free_gc_elim (pf_gc)
  val () = (!p := x)
in
  ref_make_view_ptr (pf_at | p)
end // end of [ref_make_elt]

(* ****** ****** *)

// [int64] is the type for 64-bit integers in ATS
typedef counter = '{ // the type for counter objects
  get= () -<cloref1> int64 // get the value of the counter
, set= int64 -<cloref1> void // set the value of the counter
, inc= () -<cloref1> void // increase the value of the counter
, dec= () -<cloref1> void // decrease the value of the counter
}

fn counter_make (): counter = let
  // [int64_of_int] coerce an integer into a 64-bit integer
  val r = ref_make_elt<int64> (int64_of_int 0)
in '{ // record creation
  get= lam () => !r // read from [r]
, set= lam (x) => !r := x // write to [r]
, inc= lam () => !r := succ !r
, dec= lam () => !r := pred !r
} end // end of [counter_make]

(* ****** ****** *)

// test

implement main (argc, argv) = let
  val cnt = counter_make ()
  val x = int64_of_int (1024 * 1024); val xx = x * x // 2 ^ 40
in
  print "cnt.get () = "; print (cnt.get ()); print_newline ();
  cnt.set (xx) ;
  print "cnt.get () = "; print (cnt.get ()); print_newline ();
  cnt.inc ();
  print "cnt.get () = "; print (cnt.get ()); print_newline ();
  cnt.dec ();
  print "cnt.get () = "; print (cnt.get ()); print_newline ();
end // end of [main]

(* ****** ****** *)

(* end of [references.dats] *)
