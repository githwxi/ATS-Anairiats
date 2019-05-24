(*
** some testing code for the quicksort function declared in
** contrib/glib/SATS/gstring.sats
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December, 2011
//
(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libc/SATS/string.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload _(*anon*) = "contrib/glib/DATS/glib.dats"

(* ****** ****** *)

implement
main () = {
  val n = g_utf8_strlen_cstr
    ("abcdefghijklmnopqrstuvwxyz")
  val () = println! ("n = ", $UN.cast2size (n))
} // end of [main]

(* ****** ****** *)

(* end of [gunicode-test.dats] *)

