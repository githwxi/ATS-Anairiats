//
// ProjectEuler: Problem 53
// Finding the number of C (n,r) >= 1M for 0 <= r <= n <= 100
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/matrix.dats"

(* ****** ****** *)

#define N 100
#define N1 %(N+1)
#define NROW N1
#define NCOL N1
val theTable = matrix_make_elt<int> (NROW, NCOL, 0)

#define _1M 1000000
//
// choose (n, r) = min (_1M, C(n,r))
//
fun choose
  {n,r:int | 0 <= r; r <= n; n <= N} .<n>.
  (n: int n, r: int r): int = let
  val res = theTable[n,NCOL,r]
in
  if res = 0 then let
    val res = (
      if r = 0 then 1
      else if r = n then 1
      else let
        val res = choose (n-1, r) + choose (n-1, r-1)
      in
        min (_1M, res)
      end // end of [if]
    ) : int // end of [val]
    val () = theTable[n,NCOL,r] := res
  in
    res
  end else res // end of [if]
end // end of [choose]

(* ****** ****** *)

implement
main () = () where {
  fn* loop1 (i: natLte N1, cnt: int): int =
    if i < N1 then loop2 (i, 0, cnt) else cnt
  and loop2 {i:nat | i <= N}
    (i: int i, j: natLte i, cnt: int): int =
    if j < i then let
      val Cij = choose (i, j)
      val cnt = (if Cij >= _1M then cnt+1 else cnt): int
    in
      loop2 (i, j+1, cnt)
    end else loop1 (i+1, cnt)
  // end of [loop2]
  val ans = loop1 (1, 0)
  val () = assert_errmsg (ans = 4075, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem53-hwxi.dats] *)
