//
// ProjectEuler: Problem 164
// How many 20-digit long numbers are there such that the sum of any 3 digits
// in a row does not exceed 9.
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

typedef T = ullint
val theTable1 = array_make_elt<T> (100, 0ULL)
val theTable2 = array_make_elt<T> (100, 0ULL)

(* ****** ****** *)

fun initialize () = let
  fn* loop1
    {i:nat | i <= 10} .<10-i,11>.
    (i: int i): void =
    if i < 10 then loop2 (i, 0) else ()
  and loop2
    {i,j:nat | i < 10; i+j <= 10} .<10-i,10-j>.
    (i: int i, j: int j): void = let
    val k = 10 - (i+j)
  in
    if k > 0 then let
      val () = theTable1[10*i+j] := ullint_of_int (k) in loop2 (i, j+1)
    end else loop1 (i+1)
  end // end of [loop2]
in
  loop1 (0)
end // end of [initialize]

(* ****** ****** *)

fun transfer () = let
  fn* loop1
    {i:nat | i <= 10} .<10-i,11>.
    (i: int i): void =
    if i < 10 then loop2 (i, 0) else ()
  and loop2
    {i,j:nat | i < 10; i+j <= 10} .<10-i,10-j>.
    (i: int i, j: int j): void = let
    val k = 10 - (i+j)
  in
    if k > 0 then let
      val n = 10*i+j
      val () = theTable1[n] := theTable2[n]
      val () = theTable2[n] := 0ULL
    in
      loop2 (i, j+1)
    end else loop1 (i+1)
  end // end of [loop2]
in
  loop1 (0)
end // end of [transfer]

(* ****** ****** *)

fun update () = let
  fn* loop1
    {i:nat | i <= 10} .<10-i,11,0>.
    (i: int i): void =
    if i < 10 then loop2 (i, 0) else ()
  and loop2
    {i,j:nat | i < 10; i+j <= 10} .<10-i,10-j,11>.
    (i: int i, j: int j): void = let
    val k = 10 - (i+j)
  in
    if k > 0 then loop3 (i, j, 0) else loop1 (i+1)
  end // end of [loop2]
  and loop3
    {i,j,k:nat | i < 10; i+j < 10; i+j+k <= 10} .<10-i,10-j,10-k>.
    (i: int i, j: int j, k: int k): void =
    if (i+j+k < 10) then let
      val n = 10*i+j
      val () = theTable2[n] := theTable2[n] + theTable1[10*j+k]
    in
      loop3 (i, j, k+1)
    end else loop2 (i, j+1)
  val () = loop1 (0)
  val () = transfer ()
in
  // nothing
end // end of [update]

(* ****** ****** *)

#define NDIGIT 20

implement
main () = () where {
  val () = initialize ()
  var t: int
  val () = for (t := 4; t <= NDIGIT; t := t+1) update ()
  var i: Nat = 0 and j: Nat = 0
  var sum: ullint = 0ULL
  val () =
    for (i := 1; i < 10; i := i+1)
    for (j := 0; i+j < 10; j := j+1)
      (sum := sum + theTable1[10*i+j])
  val ans = sum
  val () = assert_errmsg (ans = 378158756814587ULL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem164-hwxi.dats] *)
