// This implementation should be compiled from the above one
// in a straightforward manner (except the value of NFIB):

fun fib (nfib:int): int = begin
  (if nfib > 1 then fib (nfib-1)+ fib (nfib-2) else nfib)
end // end of [fib]

fn fib_usage (cmd: string): void = begin
  prerr ("Usage:\n");
  prerrf ("  single core: %s [integer]\n", @(cmd));
  prerrf ("  multiple core: %s [integer(arg)] [integer(core)]\n", @(cmd));
end

implement main (argc, argv) = begin
  if argc >= 2 then let
    val nfib = int_of argv.[1] // turning string into integer
    val res = fib nfib
  in
    printf ("fib (%i) = %i\n", @(nfib, res))
  end else begin
    fib_usage argv.[0]; exit (1)
  end
end // end of [main]

(* ****** ****** *)

(* end of [fib.dats] *)
