//
// ProjectEuler: Problem 157
// Finding the solutions to the Diophantine equation 1/a+1/b = p/10^n,
// where n ranges from 1 to 9
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

fun pow (x: int, n: int): int =
  if n > 0 then x * pow (x, n-1) else 1
// end of [pow]

fun ndivisor
  (x: int): int = let
  fun aux1 (
      x: int, d: int, res: int
    ) : int =
    if (x >= 2) then (
      if x mod d = 0 then let
        val q = x / d in aux2 (q, d, 1, res)
      end else aux1 (x, d+1, res)
    ) else res // end of [if]
  // end of [aux1]
  and aux2 (
      x: int, d: int, n: int, res: int
    ) : int =
    if x mod d = 0 then let
      val q = x / d in aux2 (q, d, n+1, res)
    end else aux1 (x, d+1, res * (n+1))
  // end of [aux2]
in
  aux1 (x, 2, 1)
end // end of [ndivisor]

(* ****** ****** *)

// val ans = ndivisor (pow(2, 10) * pow (5, 9))
// val () = (print "ans = "; print ans; print_newline ())

(* ****** ****** *)

fun eval
  (n: int): int = let
  var res: int = 0
  val _2_n = pow (2, n)
  val _5_n = pow (5, n)
  val _10_n = _2_n * _5_n
  var i: int = 0 and j: int = 0
  val () =
    for (i := 0; i <= n; i := i+1)
    for (j := 0; j <= n; j := j+1) let
      val base = pow (2, i) * pow (5, j) in res := res + ndivisor (_10_n + base)
    end // ...
  // end of [val]
  val () =
    for (i := 0; i < n; i := i+1)
    for (j := 0; j < n; j := j+1) let
      val base1 = pow (2, i) * _5_n
      val base2 = _2_n * pow (5, j)
    in
      res := res + ndivisor (base1 + base2)
    end // ...
  // end of [val]
in
  res (* the return value *)
end // end of [eval]

(* ****** ****** *)

implement
main () = let
  var res: int = 0
  var i: int
  val () = for
    (i := 1; i <= 9; i := i+1) let
    val res1 = eval i
(*
    val () = (print "res1 = "; print res1; print_newline ())
*)
  in
    res := res + res1
  end
  val ans = res
in
  print "ans = "; print ans; print_newline ()
end // end of [main]

(* ****** ****** *)

(* end of [problem157-hwxi] *)
