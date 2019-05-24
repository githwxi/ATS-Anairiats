(*
//
// Some code for testing the Enigma simulator
//
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/random.sats"

(* ****** ****** *)

staload "enigma.sats"

(* ****** ****** *)

dynload "enigma.dats"

(* ****** ****** *)

implement
main () = {
//
#define nil list_nil
#define :: list_cons
//
  val () = srand48 (1000000L)
//
  val E = enigma_make_rand (5)
//
  fn f (c: char):<cloref1> char =
    if c >= 'a' andalso c <= 'z' then let
      val n = c - 'a'
      val n = abrange_of_int (n)
      val v = enigma_encode (E, n)
      val v = int_of_abrange (v)
    in
      char_of_int (int_of 'a' + v)
    end else c // end of [if]
//
  val () =
    loop (stdin_ref) where {
    fun loop
      (fil: FILEref):<cloref1> void = let
      val c = fgetc_err (fil)
    in     
      if c >= 0 then let
        val c = (char_of_int)c
        val () = fputc_exn (f(c), stdout_ref)
      in
        loop (fil)
      end // end of [if]
    end // end of [loop]
  } (* end of [val] *)
} // end of [main]

(* ****** ****** *)

(* end of [test2.dats] *)
