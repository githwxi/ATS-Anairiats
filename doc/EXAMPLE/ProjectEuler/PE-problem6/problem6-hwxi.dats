//
// ProjectEuler: Problem 6
// Finding the difference (1+...+n)^2 - (1^2+...+n^2)
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010 // the first solution
//

(* ****** ****** *)

fn sumf {n:nat}
  (n: int n, f: int -<fun> int):<> int = let
  fun loop {i:nat} .<n+1 nsub i>.
    (i: int i, res: int):<cloref> int =
    if i <= n then loop (i+1, res + f(i)) else res
  // end of [loop]
in
  loop (1, 0(*init*))
end // end of [sumf]

(* ****** ****** *)

implement main () = () where {
  #define N 100
  val sum1 = sumf {..} (N, lam x => x)
  val sum2 = sumf {..} (N, lam x => x * x)
  val ans = sum1 * sum1 - sum2
  val () = assert (ans = square (N*(N+1)/2) - N*(N+1)*(2*N+1)/6)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem6-hwxi.dats] *)
