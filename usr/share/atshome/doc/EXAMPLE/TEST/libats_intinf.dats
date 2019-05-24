(*
** some testing code for functions declared in
** libats/SATS/intinf.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Spring, 2009
//

(* ****** ****** *)

staload "libats/SATS/intinf.sats"

(* ****** ****** *)

fun fact
  (x: int): Intinf =
  loop (x, res) where {
  val x = int1_of_int x
  val res = intinf_make (1)
  fun loop {i:int} (
    x: int i, res: Intinf
  ) : Intinf =
    if x > 0 then let
      val (pf_mul | res1) = res * x
      val () = intinf_free (res)
    in
      loop (x - 1, res1)
    end else res // end of [if]
  // end of [loop]
} // end of [fact]

fn prerr_usage (cmd: string): void =
  prerrf ("Usage: %s <integer>\n", @(cmd))
// end of [prerr_usage]

(* ****** ****** *)

dynload "libats/DATS/intinf.dats"

implement main (argc, argv) = let
  val () = if (argc <> 2) then prerr_usage (argv.[0])
  val () = assert (argc = 2)
  val n = int1_of_string (argv.[1])
  val res = fact (n)
  val () = begin
    printf ("fact (%i) = ", @(n)); print (res); print_newline ()
  end // end of [val]
  val () = intinf_free (res)
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [libats_intinf.dats] *)
