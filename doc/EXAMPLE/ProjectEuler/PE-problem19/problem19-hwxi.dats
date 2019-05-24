//
// ProjectEuler: Problem 19
// Finding the number of sundays fell on the
// first of a month during the 20th century.
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

fn isLeap (y: int) =
  if (y mod 4 = 0) then
    if (y mod 100 <> 0) then true else (y mod 400 = 0)
  else false
// end of [isLeap]

(* ****** ****** *)

val x_1900_01_01: int = 1 // 1900-01-01: Monday
val x_1901_01_01: int = let
  val n = (if isLeap (1900) then 365+1 else 365): int
in
  (x_1900_01_01 + n) mod 7
end // end of [val]

(* ****** ****** *)

implement
main () = () where {
  #define SUNDAY 0
  var cnt: int = 0
  val y0 = 1901 and y1 = 2000
  var x: int = x_1901_01_01
  var y: int
  val () = for
    (y := y0; y <= y1; y := y+1) let
    val () = if (x = SUNDAY) then cnt := cnt + 1 // JAN
    val () = x := (x + 31) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // FEB
    val () = if isLeap (y) then x := (x+29) mod 7 else x := (x+28) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // MAR
    val () = x := (x + 31) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // APR
    val () = x := (x + 30) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // MAY
    val () = x := (x + 31) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // JUN
    val () = x := (x + 30) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // JUL
    val () = x := (x + 31) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // AUG
    val () = x := (x + 31) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // SEP
    val () = x := (x + 30) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // OCT
    val () = x := (x + 31) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // NOV
    val () = x := (x + 30) mod 7
//
    val () = if (x = SUNDAY) then cnt := cnt + 1 // DEC
    val () = x := (x + 31) mod 7
//
  in
    // nothing
  end // end of [val]
  val ans = cnt
  val () = assert_errmsg (ans = 171, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem19-hwxi.dats] *)
