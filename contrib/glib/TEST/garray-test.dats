(*
** some testing code for the quicksort function declared in
** contrib/glib/SATS/garray.sats
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2010
//
(* ****** ****** *)

#include "contrib/glib/HATS/glibconfig.hats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload _(*anon*) = "contrib/glib/DATS/glib.dats"

(* ****** ****** *)

implement main () = () where {
  val () = begin
    print ("garray-test: starts"); print_newline ()
  end // end of [va]
//
  var i: Nat // unintialized
  var x: gint? // uninitialized
//
  #define N 100
  val garray = g_array_new {gint} (GFALSE, GFALSE, sizeof<gint>)
  val () = for
    (i := 0; i < N; i := i + 1) (x := gint(i); g_array_append_val (garray, x))
  // end of [val]
  val () = for
    (i := 0; i < N; i := i + 1)
    assert_errmsg (g_array_get_elt_at<gint> (garray, (gint)i) = (gint)i, #LOCATION)
  // end of [val]
//
#if ATSCTRB_GLIB_VERSION >= 2022000 #then
    val () = g_array_unref (garray)
#else
    val () = g_array_free_true (garray)
#endif // end of [ATSCTRB_GLIB_VERSION]
//
  #define N 100
  val garray = g_array_new {gint} (GFALSE, GFALSE, sizeof<gint>)
  val () = for
    (i := 0; i < N; i := i + 1) (x := gint(i); g_array_prepend_val (garray, x))
  // end of [val]
  val () = for
    (i := 0; i < N; i := i + 1)
    assert_errmsg (g_array_get_elt_at<gint> (garray, (gint)(i)) = (gint)(N-i-1), #LOCATION)
  // end of [val]
  val () = g_array_free_true (garray)
//
  val () = begin
    print ("garray-test: finishes"); print_newline ()
  end // end of [va]
} // end of [main]

(* ****** ****** *)

(* end of [garray-test.dats] *)
