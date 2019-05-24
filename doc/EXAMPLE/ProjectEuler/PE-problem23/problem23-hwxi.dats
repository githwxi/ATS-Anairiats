//
// ProjectEuler: Problem 23
// Finding the sum of all the numbers that cannot be represented
// as the sum of two abundant numbers
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array0.dats"

(* ****** ****** *)

fun sumdiv (n: int): int = let
 fun loop1 (n: int, p: int): int =
   if p * p <= n then let
     val r = n mod p
   in
     if r = 0 then loop2 (n/p, p, 1) else loop1 (n, p+1)
   end else n+1
 // end of [loop1]
 and loop2 (n: int, p: int, acc: int): int = let
   val r = n mod p
 in
   if r = 0 then loop2 (n/p, p, 1 + acc * p) else sumdiv (n) * (1 + acc * p)
 end // end of [loop2]
in
  if n >= 2 then loop1 (n, 2) else 1
end // end of [sumdiv]

(* ****** ****** *)

#define N 28123
val MEMO = array0_make_elt<int> (N, ~1) // for memoization
fun isAbundant
  (n: int): bool = let
  val tag = MEMO[n] in
  if tag >= 0
    then tag > 0 else let
    val ans = sumdiv (n) > (n + n) 
    val tag = (if ans then 1 else 0): int
    val () = MEMO[n] := tag
  in
    ans
  end // end of [if]
end // end of [isAbundant]

(* ****** ****** *)

fun test (x: int): bool = let
  fun loop (x: int, i: int): bool =
    if i + i <= x then
      if (isAbundant (i) andalso isAbundant (x-i)) then true else loop (x, i+1)
    else false
in
  loop (x, 12) // 12 is the first abundant number
end // end of [test]

(* ****** ****** *)

implement
main () = () where {
  var sum: int = 0
  var x: int // uninitialized
  val () = for
    (x := 1; x < N; x := x + 1) let
    val () = if ~test(x) then sum := sum + x in (*nothing*)
  end // end of [val]
  val ans = sum
  val () = assert_errmsg (ans = 4179871, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem23-hwxi.dats] *)
