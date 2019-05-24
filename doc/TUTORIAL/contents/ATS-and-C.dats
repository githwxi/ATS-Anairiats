//
// An example of combining ATS code with C code
//

extern fun fibonacci (n: Nat): Nat = "fibonacci"

%{

ats_int_type fibonacci (ats_int_type n) {
  int res1, res2, tmp ;

  if (n < 1) return 0 ;
 
  res1 = 0 ; res2 = 1 ;
  while (n > 1) {
    --n ; tmp = res2 ; res2 += res1 ; res1 = tmp ;
  }

  return res2 ;
}

%}

fn fibonacci_usage (cmd: string): void =
  prerrf ("Usage: %s [integer]\n", @(cmd)) // print an error message

implement main (argc, argv) =
  if argc >= 2 then let
    val n = int1_of argv.[1] // turning string into integer
    val () = assert_errmsg
      (n >= 0, "The integer argument needs to be nonnegative.\n")
    val res = fibonacci n
  in
    printf ("fibonacci (%i) = %i\n", @(n, res))
  end else begin
    fibonacci_usage argv.[0]; exit {void} (1)
  end
// end of [main]

(* ****** ****** *)

(* end of [ATS-and-C.dats] *)
