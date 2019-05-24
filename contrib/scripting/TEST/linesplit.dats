(*
** some scripting code
*)
(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Spring, 2011
//
(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list_vt.dats"
staload _(*anon*) = "prelude/DATS/pointer.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libats/SATS/regexp.sats"
staload "contrib/scripting/SATS/scripting.sats"
staload _(*anon*) = "contrib/scripting/DATS/scripting.dats"

(* ****** ****** *)

extern
fun split {l:agz} {n:int} {i,ln:nat | i+ln <= n}
  (out: FILEref, re: !REGEXPptr l, str: string n, ofs: int i, len: int ln): void
// end of [split]

implement split (out, re, str, ofs, len) = let
  val strposlst = regexp_match_substring_strposlst (re, str, ofs, len)
in
  case+ strposlst of
  | ~list_vt_cons (ij, ijs) => let
      val (i, j) = ij
      val () = assert (i >= 0)
      val () = fprint_segment (out, str, ofs, ofs+i)
      val () = fprint_char (out, '\n')
      val () = list_vt_free (ijs)
    in
      split (out, re, str, ofs+j, len-j)
    end // end of [
  | ~list_vt_nil () => () where {
      val () = fprint_segment (out, str, ofs, ofs+len)
      val () = fprint_char (out, '\n')
    } // end of [list_vt_nil]
end // end of [split]

(* ****** ****** *)

dynload "libats/DATS/regexp.dats"
dynload "contrib/scripting/DATS/scripting.dats"

(* ****** ****** *)

implement
main () = let
  val sep = regexp_compile_exn ("\s+")
  fun loop {l:agz}
    (inp: FILEref, out: FILEref, sep: !REGEXPptr l): void = let
    val line = input_line (inp)
    val isexi = stropt_is_some (line )
  in
    if isexi then let
      val line = stropt_unsome (line)
      val n = int1_of_size1 (string_length (line))
      val () = split (out, sep, line, 0, n)
    in
      loop (inp, out, sep)
    end // end of [if]
  end // end of [loop]
  val () = loop (stdin_ref, stdout_ref, sep)
  val () = regexp_free (sep)
in
  // nothing
end // end of [main]

(* ****** ****** *)

(* end of [linesplit.dats] *)
