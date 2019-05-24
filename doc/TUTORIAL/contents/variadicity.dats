//
//
// Author: Hongwei Xi (August, 2007)
//
//

#define N 9

implement
main (argc, argv) = loop1 (0) where {
//
// [loop1] and [loop2] are verified to be terminating
// based on the supplied metrics
//
// [ .< N-i, 0 >. ] is a termination metric
// Ignore it if you have not learned this feature yet
  fun loop1
    {i:nat | i <= N} .<N-i, 0>.
    (i: int i): void =
    if i < N then loop2 (i+1, 0) else ()
  // end of [loop1]
//
// [ .<N-i, N+1-j>. ] is a termination metric
// Ignore it if you have not learned this feature yet
//
  and loop2
    {i,j:nat | i <= N; j <= i} .<N-i, i-j+1>.
    (i: int i, j: int j): void =
    if j < i then begin
      if (j > 0) then print '\t';
      printf ("%1d*%1d=%2.2d", @(j+1, i, (j+1) * i));
      loop2 (i, j+1)
    end else begin
      print_newline (); loop1 (i)
    end // end of [if]
  // end of [loop2]
} // end of [main]

(* ****** ****** *)

(* end of [variadicity.dats] *)
