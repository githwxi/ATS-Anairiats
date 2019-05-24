//
// ProjectEuler: Problem 40
// Finding nth digit in the fractional part of a given irrational number
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

fun pow10 (x: int): int =
  if x > 0 then 10 * pow10 (x-1) else 1
  
fun f (n: int) = 
  if n > 0 then 9 * (n * pow10 (n-1)) else 0
// end of [f]

fun find1
  (x: int, n: int, F_n: int): @(int, int) = let
  val n1 = n + 1
  val f_n1 = f (n1)
  val F_n1 = F_n + f_n1
in
  if x <= F_n1 then @(n, F_n) else find1 (x, n1, F_n1)
end // end of [find]

fun find2
  (x: int): int = let
  val @(n, F_n) = find1 (x, 0, 0)
  val d = x - 1 - F_n
  val n1 = n+1
  val q = d / n1
  val r = d - n1 * q
  var num: int = pow10 (n) + q
  var nr: int = n - r
  val () = while (nr > 0) (num := num / 10; nr := nr - 1)
in
  num mod 10
end // end of [find2]

(* ****** ****** *)

val d1 = find2 (1)
val d10 = find2 (10)
val d100 = find2 (100)
val d1000 = find2 (1000)
val d10000 = find2 (10000)
val d100000 = find2 (100000)
val d1000000 = find2 (1000000)
val ans = d1 * d10 * d100 * d1000 * d10000 * d100000 * d1000000
val () = assert_errmsg (ans = 210, #LOCATION)
val () = (print "ans = "; print ans; print_newline ())

(* ****** ****** *)

implement main () = ()

(* ****** ****** *)

(* end of [problem40-hwxi.dats] *)
