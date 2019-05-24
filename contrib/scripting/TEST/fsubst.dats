(*
** some scripting code
*)

(* ****** ****** *)

staload
UN = "prelude/SATS/unsafe.sats"
staload STDIO = "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "contrib/scripting/SATS/scripting.sats"

(* ****** ****** *)

dynload "libats/DATS/regexp.dats"
dynload "contrib/scripting/DATS/scripting.dats"

(* ****** ****** *)

implement
main (argc, argv) = {
  val i = 0
  val inp = stdin_ref
  val () = assert (argc >= i+3)
(*
  val inp = $STDIO.fopen_ref_exn (argv.[1], file_mode_r)
*)
  val err = fsubst_pat_string (inp, stdout_ref, argv.[i+1], argv.[i+2])
(*
  val () = $STDIO.fclose_exn (inp)
*)
  // val () = assertloc (err = 0)
} // end of [main]

(* ****** ****** *)

(* end of [fsubst.dats] *)
