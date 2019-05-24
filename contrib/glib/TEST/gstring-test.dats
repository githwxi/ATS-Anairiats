(*
** some testing code for the quicksort function declared in
** contrib/glib/SATS/gstring.sats
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2010
//
(* ****** ****** *)

#include "contrib/glib/HATS/glibconfig.hats"

(* ****** ****** *)

staload "libc/SATS/string.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload _(*anon*) = "contrib/glib/DATS/glib.dats"

(* ****** ****** *)

macdef gs = gstring_of_string

(* ****** ****** *)

fun print_gstring {l:agz}
  (gstring: !GString_ptr l): void = () where {
  val ptr = g_string_get_str (gstring)
  val string = __cast (ptr) where { extern castfn __cast (x: ptr): string }
  val () = print (string)
} // end of [print_gstring]

implement main () = () where {
  val () = begin
    print ("gstring-test: starts"); print_newline ()
  end // end of [va]
//
  val (fpf_x | x) = (gs)"abcdefghijklm"
  val gstring = g_string_new x
  prval () = fpf_x (x)
  val (fpf_x | x) = (gs)"nopqrstuvwxyz"
  val _ptr = g_string_append (gstring, x)
  prval () = fpf_x (x)
  val sgn = strcmp (string, "abcdefghijklmnopqrstuvwxyz") where {
    val ptr = g_string_get_str gstring
    val string = __cast (ptr) where { extern castfn __cast (p: ptr): string }
  } // end of [val]
  val () = assert_errmsg (sgn = 0, #LOCATION)
  val () = g_string_printf (gstring, "%s, %s!\n", @("Hello", "world"))
  val () = print_gstring (gstring)
  val () = g_string_free_true (gstring)
//
  val gstring = g_string_new_null ()
  val (fpf_x | x) = (gs) "Hello"
  val _ptr = g_string_append (gstring, x)
  prval () = fpf_x (x)
  val _ptr = g_string_append_c (gstring, (gchar)',')
  val () = g_string_append_printf (gstring, " %s!\n", @("world"))
  val () = print_gstring (gstring)
  val () = g_string_free_true (gstring)
//
  val gstring = g_string_new_null ()
  val _ptr = g_string_prepend (gstring, "world!\n")
  val _ptr = g_string_prepend_c (gstring, (gchar)' ')
  val _ptr = g_string_prepend (gstring, "Hello,")
  val () = print_gstring (gstring)
  val () = g_string_free_true (gstring)
//
  val (fpf_x | x) = (gs)"Hello  world!"
  val gstring = g_string_new_init (x)
  prval () = fpf_x (x)
  val n = string1_length "Hello"
  val _ptr = g_string_erase (gstring, (gssize)n, (gssize)2)
  val _ptr = g_string_insert (gstring, (gssize)n, ", ")
  val _ptr = g_string_insert_c (gstring, (gssize)~1, (gchar)'\n')
  val () = print_gstring (gstring)
  val _ptr = g_string_truncate (gstring, (gsize)n)
  val () = print_gstring (gstring)
  val () = print_newline ()
  val _ptr = g_string_set_size (gstring, (gsize)((n+1)/2))
  val () = print_gstring (gstring)
  val () = print_newline ()
  val () = g_string_free_true (gstring)
//
#if ATSCTRB_GLIB_VERSION >= 2014000 // since glib-2.14
  val gstring = gstring where {
    val (fpf_cs | cs) =
      (gs)"Hello  world!"
    val gstring = g_string_new_init (cs)
    prval () = fpf_cs (cs)
  } // end of [val]
  val n = string1_length "Hello"
  val _ptr = g_string_overwrite (gstring, (gssize)n, ", ")
  val _ptr = g_string_append_c (gstring, (gchar)'\n')
  val () = print_gstring (gstring)
  val () = g_string_free_true (gstring)
#endif // end of [ATSCTRB_GLIB_VERSION]
//
  val () = begin
    print ("gstring-test: finishes"); print_newline ()
  end // end of [va]
} // end of [main]

(* ****** ****** *)

(* end of [gstring-test.dats] *)
