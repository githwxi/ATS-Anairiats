//
// ProjectEuler: Problem 18
// Finding the maximal sum traveling from the top of a triangle to the base
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/matrix0.dats"

(* ****** ****** *)

(*
75
95 64
17 47 82
18 35 87 10
20 04 82 47 65
19 01 23 75 03 34
88 02 77 73 07 63 67
99 65 04 28 06 16 70 92
41 41 26 56 83 40 80 70 33
41 48 72 33 47 32 37 16 94 29
53 71 44 65 25 43 91 52 97 51 14
70 11 33 28 77 73 17 78 39 68 17 57
91 71 52 38 17 14 91 43 58 50 27 29 48
63 66 04 68 89 53 67 30 73 16 69 87 40 31
04 62 98 27 23 09 70 98 73 93 38 53 60 04 23
*)

val theInp = "\
75\
95 64\
17 47 82\
18 35 87 10\
20 04 82 47 65\
19 01 23 75 03 34\
88 02 77 73 07 63 67\
99 65 04 28 06 16 70 92\
41 41 26 56 83 40 80 70 33\
41 48 72 33 47 32 37 16 94 29\
53 71 44 65 25 43 91 52 97 51 14\
70 11 33 28 77 73 17 78 39 68 17 57\
91 71 52 38 17 14 91 43 58 50 27 29 48\
63 66 04 68 89 53 67 30 73 16 69 87 40 31\
04 62 98 27 23 09 70 98 73 93 38 53 60 04 23\
"
val theLen = string1_length (theInp)

val theNROW = ref<int> (0)
val theList = aux (1, 0, 0) where {
  fun aux {i:nat}
    (n0: int, n: int, i: int i): List (int) =
    if i + 2 <= theLen then let
      val d1 = theInp[i] - '0' and d2 = theInp[i+1] - '0'
      val x = 10 * d1 + d2
      val xs = (
        if n > 0 then aux (n0, n-1, i+3) else (!theNROW := n0; aux (n0+1, n0, i+2))
      ) : List (int)
    in
      list_cons (x, xs)
    end else list_nil // end of [if]
  // end of [aux]
} // end of [val]

val N = !theNROW
val N = int1_of_int (N)
val () = assert (N >= 0)
val NSZ = size_of_int1 (N)
(*
val () = (print "N = "; print N; print_newline ())
val () = list_foreach_cloref<int> (theList, lam x =<1> $effmask_ref (print x))
val () = print_newline ()
*)

(* ****** ****** *)

val MAT = matrix0_make_elt<int> (NSZ, NSZ, 0)
val () = loop (0, 0, theList) where {
  fun loop {i,j:nat}
    (i: int i, j: int j, xs: List int): void =
    if j <= i then let
      val- list_cons (x, xs) = xs
      val () = MAT[i,j] := x
    in
      loop (i, j+1, xs)
    end else begin
      if i < N-1 then loop (i+1, 0, xs) else ()
    end // end of [if]
  // end of [loop]
} // end of [val]
(*
val () = () where {
  val f = lam (i: size_t, j: size_t, x: &int)
    : void =<cloref> let
    val i = int_of_size i and j = int_of_size j
  in
    if j <= i then let
      val () = $effmask_all (if j > 0 then print ' ')
      val () = $effmask_all (printf ("%2.2i", @(x)))
      val () = $effmask_all (if j >= i then print '\n')
    in
      // nothing
    end // end of [if]
  end // end of [f]
  val () = matrix0_iforeach (MAT, f)
} // end of [val]
*)

(* ****** ****** *)

fun eval
  (i: int, j: int, n: int): int =
  if n > 0 then let
    val res1 = eval (i+1, j, n-1)
    val res2 = eval (i+1, j+1, n-1)
    val res = max (res1, res2)
  in
    MAT[i,j] + res
  end else MAT[i,j]
// end of [eval]

(* ****** ****** *)

implement
main () = () where {
  val ans = eval (0, 0, N-1)
  val () = assert_errmsg (ans = 1074, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem18-hwxi.dats] *)
