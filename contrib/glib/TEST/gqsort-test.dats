(*
** some testing code for the quicksort function declared in
** contrib/glib/SATS/gqsort.sats
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2010
//
(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"

(* ****** ****** *)

%{^
#define SIZE 1000000 // 1 million
static guint32 array[SIZE];
%} // end of [%{^]
#define SIZE 1000000 // 1 million
sta l_array : addr
val p_array = $extval (ptr l_array, "&array[0]")
extern prval pf_array : vbox (array_v (guint32, SIZE, l_array))

(* ****** ****** *)

fun test () = () where {
  var i: Nat
  prval vbox pf = pf_array
  val () = begin
    for (i := 0; i < SIZE; i := i+1)
      p_array->[i] := $effmask_ref (g_random_int ())
    // end of [for]
  end // end of [val]
  val () = $effmask_ref begin
    print ("gqsort-test: initialization is done"); print_newline ()
  end // end of [val]
  val () = g_qsort_with_data {guint32} {ptr} (
    !p_array
  , (gint)SIZE
  , sizeof<guint32>
  , lam (x, y, _env) => gint ((if x < y then ~1 else 1): Int)
  , null
  ) // end of [val]
  val () = $effmask_ref begin
    print ("gqsort-test: sorting is done"); print_newline ()
  end // end of [val]
  val () = begin
    for (i := 0; i < SIZE-1; i := i+1)
      assert_errmsg (p_array->[i] <= p_array->[i+1], #LOCATION)
    // end of [for]
  end
  val () = $effmask_ref begin
    print ("gqsort-test: verification is done"); print_newline ()
  end // end of [val]
} // end of [test]

implement main () = () where {
  val () = begin
    print ("gqsort-test: starts"); print_newline ()
  end // end of [va]
//
  val () = test ()
//
  val () = begin
    print ("gqsort-test: finishes"); print_newline ()
  end // end of [va]
} // end of [main]

(* ****** ****** *)

(* end of [gqsort-test.dats] *)
