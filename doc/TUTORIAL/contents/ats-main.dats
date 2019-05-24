//
//
// code for illustration in ats-main.html
//
//

implement main (argc, argv) = let
  fun loop {n,i:nat | i <= n} // [loop] is tail-recursive
    (i: int i, argc: int n, argv: &(@[string][n])): void =
    if i < argc then begin
      if i > 0 then print (' '); print argv.[i]; loop (i+1, argc, argv)
    end // end of [if]
  // end of [loop]
in
  loop (0, argc, argv); print_newline ()
end // end of [main]

(* ****** ****** *)

(* end of [ats-main.dats] *)
