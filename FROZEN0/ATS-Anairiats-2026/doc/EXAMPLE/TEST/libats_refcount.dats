(*

// some testing code for [libats/refcount]

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December, 2011

*)

(* ****** ****** *)

staload "libats/SATS/refcount.sats"
staload _(*anon*) = "libats/DATS/refcount.dats"

(* ****** ****** *)

viewtypedef strnref = nref (strptr0)

(* ****** ****** *)

fun fprint_strnref (
  out: FILEref, x: !strnref
) : void = let
  val (pf | p) = refcount_takeout (x)
  val () = fprint_strptr (out, !p)
  prval () = refcount_addback (pf | x)
in
 // nothing
end // end of [fprint_strnref]

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

implement
main () = () where {
//
  val msg = "Hello, world!\n"
  val nmsg = string1_length (msg)
  val str = string_make_substring (msg, 0, nmsg)
  val str = strptr_of_strbuf (str)
//
  val r = refcount_make<strptr0> (str)
  val p = $UN.castvwtp1 {ptr} (r)
  val () = assert (1u = refcount_get_count r)
//
  val () = fprint_strnref (stdout_ref, r)
//
  val r1 = refcount_ref (r)
  val () = assert (2u = refcount_get_count (r))
//
  stadef T = strptr0
  var x: T?
//
  val ans = refcount_unref (r, x)
  val () = assert (ans = false)
  prval () = opt_unnone {T} (x)
  val () = assert (1u = refcount_get_count (r1))
//
  val () = fprint_strnref (stdout_ref, r1)
//
  val ans = refcount_unref (r1, x)
  val () = assert (ans = true)
  prval () = opt_unsome {T} (x)
//
  val () = strptr_free (x)
//
} // end of [main]

(* ****** ****** *)

(* end of [libats_refcount.dats] *)
