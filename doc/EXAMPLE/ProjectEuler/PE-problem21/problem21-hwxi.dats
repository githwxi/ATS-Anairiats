//
// ProjectEuler: Problem 21
// Finding the sum of all the amicable pairs under 10000
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

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

#define N 10000

implement
main () = () where {
  var sum: int = 0
  var i: int // uninitialized
  val () = for
    (i := 2; i < N; i := i + 1) let
    val s1 = sumdiv (i) - i
  in
    if s1 < i then let
      val s2 = sumdiv (s1) - s1
    in
      if i = s2 then let
(*
        val () = printf ("s1 = %i and s2 = %i\n", @(s1, s2))
*)
      in
        sum := sum + (s1 + s2)
      end // end of [if]
    end // end of [if]
  end // end of [for]
  val ans = sum
  val () = assert_errmsg (ans = 31626, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem21-hwxi.dats] *)
