//
// ProjectEuler: Problem 17
// Finding the number of English letters needed to write 1, 2, ..., 999 and 1000
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

macdef length = string_length

(* ****** ****** *)

fun name1
  {n:int | 1 <= n; n <= 9} (n: int n): string =
  case+ n of
  | 1 => "one"
  | 2 => "two"
  | 3 => "three"
  | 4 => "four"
  | 5 => "five"
  | 6 => "six"
  | 7 => "seven"
  | 8 => "eight"
  | 9 => "nine"
// end of [name1]

fun name2
  {n:int | 10 <= n; n <= 19} (n: int n): string =
  case+ n of
  | 10 => "ten"
  | 11 => "eleven"
  | 12 => "twelve"
  | 13 => "thirteen"
  | 14 => "fourteen"
  | 15 => "fifteen"
  | 16 => "sixteen"
  | 17 => "seventeen"
  | 18 => "eighteen"
  | 19 => "nineteen"
// end of [name1]

fun name3
  {n:int | 2 <= n; n <= 9} (n: int (n)): string =
  case+ n of
  | 2 => "twenty"
  | 3 => "thirty"
  | 4 => "forty"
  | 5 => "fifty"
  | 6 => "sixty"
  | 7 => "seventy"
  | 8 => "eighty"
  | 9 => "ninety"
// end of [name3]

(* ****** ****** *)

val sum_1_9 = let
  fun loop
    {i:int | 1 <= i; i <= 10} .<10-i>.
    (i: int i, sum: size_t): size_t =
    if i < 10 then loop (i+1, sum + length (name1 (i))) else sum
  // end of [loop]
in
  loop (1, 0)
end // end of [val]

val () = (print "sum_1_9 = "; print sum_1_9; print_newline ())

(* ****** ****** *)

val sum_10_19 = let
  fun loop
    {i:int | 10 <= i; i <= 20} .<20-i>.
    (i: int i, sum: size_t): size_t =
    if i < 20 then loop (i+1, sum + length (name2 (i))) else sum
  // end of [loop]
in
  loop (10, 0)
end // end of [val]

val () = (print "sum_10_19 = "; print sum_10_19; print_newline ())

(* ****** ****** *)

val sum10_2_9 = let
  fun loop
    {i:int | 2 <= i; i <= 10} .<10-i>.
    (i: int i, sum: size_t): size_t =
    if i < 10 then loop (i+1, sum + length (name3 (i))) else sum
  // end of [loop]
in
  loop (2, 0)
end // end of [val]

val () = (print "sum10_2_9 = "; print sum10_2_9; print_newline ())

(* ****** ****** *)

val sum_1_99 = sum_1_9 + sum_10_19 + 10 * sum10_2_9 + 8 * sum_1_9
val sum_1_999 =
  100 * sum_1_9 + 900 * length"hundredand" - 9 * length"and" + 10 * sum_1_99
// end of [sum_1_999]

(* ****** ****** *)

val ans = sum_1_999 +  length"onethousand"
val () = assert_errmsg (ans = 21124, #LOCATION)
val () = (print "ans = "; print ans; print_newline ())

(* ****** ****** *)

implement main () = ()

(* ****** ****** *)

(* end of [problem17-hwxi.dats] *)
