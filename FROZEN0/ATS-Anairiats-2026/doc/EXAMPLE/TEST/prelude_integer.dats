(*
** some testing code for functions declared in
** prelude/SATS/integer.sats
*)
(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: April, 2012
//
(* ****** ****** *)
//
// staload "prelude/SATS/integer.sats"
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/pointer.dats"

(* ****** ****** *)

staload "libc/SATS/signal.sats"
staload "libc/SATS/unistd.sats"

(* ****** ****** *)

fun fhandler (
  sgn: signum_t
) : void = let
  val () = print (
    "No input was given in the allowed amount time."
  ) // end of [val]
  val () = print_newline ()
in
  exit (0)
end // end of [fhandler]

implement
main () = {
//
  var act: sigaction
  val () =
    ptr_zero<sigaction>
      (__assert () | act) where {
    extern prfun __assert (): NULLABLE (sigaction)
  } // end of [val]
  val () = act.sa_handler := (sighandler)fhandler
  val err = sigaction_null (SIGALRM, act)
//
  var i: int
  val () = fprintf (stdout_ref, "Please input an integer:\n", @())
  val (pf | n) = alarm_set (10u)
  val () = fscan_int_exn (stdin_ref, i)
  val _leftover = alarm_cancel (pf | (*none*))
  val () = fprintf (stdout_ref, "The input integer is [%d]\n", @(i))
} // end of [main]

(* ****** ****** *)

(* end of [prelude_integer.dats] *)
