//
// ProjectEuler: Problem 15
// Starting from the top left corner of a 20x20 grid, how many
// routes are there to the bottom right corner?
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

//
// HX-2010-09-17:
// this one is taken from Matthias Berndt (matthias_berndt AT gmx DOT de)
//
dataprop PATHS(int, int, int) =
  | {y: nat} PATHSbas1(0, y, 1)
  | {x: nat} PATHSbas2(x, 0, 1)
  | {x, y, z1, z2: nat} PATHSind(x+1, y+1, z1+z2) of (PATHS(x, y+1, z1), PATHS(x+1, y, z2))
// end of [PATHS]

(* ****** ****** *)

//
// HX: A representation good for 64-bit unsigned integers
//
symintr ullint1
extern castfn ullint1_int {i:nat} (x: int i):<> ullint (i)
overload ullint1 with ullint1_int
//
extern fun print_ullint1
  {i:nat} (x: ullint i): void = "atspre_print_ullint"
overload print with print_ullint1
extern fun add_ullint1_ullint1
  {z1,z2:nat} (z1: ullint z1, z2: ullint z2):<> ullint (z1+z2)
  = "atspre_add_ullint_ullint"
overload + with add_ullint1_ullint1

(* ****** ****** *)

typedef T (x: int, y: int) = [z:nat] (PATHS (x, y, z) | ullint z)

(* ****** ****** *)

//
// HX: this one is correct, but hopelessly inefficient!
//
fun f1 {x,y:nat} .<x+y>.
  (x: int x, y: int y):<> T (x, y) =
  if x = 0 then
    (PATHSbas1 () | (ullint1)1)
  else if y = 0 then
    (PATHSbas2 () | (ullint1)1)
  else let
    val (pf1 | z1) = f1 (x-1, y)
    val (pf2 | z2) = f1 (x, y-1)
  in
    (PATHSind (pf1, pf2) | z1+z2)
  end // end of [if]
// end of [f1]

(* ****** ****** *)

typedef mfun_t = {x,y:nat}
  (int x, int y, Option (T (x, y))) -<> Option (T (x, y))
// end of [mfun_t]

//
// HX: this one makes use of memoization
//
fun f2 {x,y:nat}
  (x: int x, y: int y, m: mfun_t): T (x, y) = let
  val ores = m (x, y, None ())
in
  case+ ores of
  | Some (res) => res
  | None () => let
      val res = (if x = 0 then
        (PATHSbas1 () | (ullint1)1)
      else if y = 0 then
        (PATHSbas2 () | (ullint1)1)
      else let
        val (pf1 | z1) = f2 (x-1, y, m)
        val (pf2 | z2) = f2 (x, y-1, m)
      in
        (PATHSind (pf1, pf2) | z1 + z2)
      end ) : T (x, y) // end of [if]
      val ores = Some (res)
      val _ = m (x, y, ores)
    in
      res
    end // end of [None
end // end of [f2]

(* ****** ****** *)

extern
fun theMemoTable_get
  {x,y:nat} (x: int x, y: int y):<> Option (T (x, y)) = "theMemoTable_get"
extern
fun theMemoTable_set
  {x,y:nat} (x: int x, y: int y, z: T (x, y)):<> void = "theMemoTable_set"

fun mfun {x,y:nat} .<>.
  (x: int x, y: int y, ores: Option (T (x, y))):<> Option (T (x, y)) =
  case+ ores of
  | None () => theMemoTable_get (x, y)
  | Some res => let
      val () = theMemoTable_set (x, y, res) in None ()
    end // end of [Some]
// end of [mfun]

(* ****** ****** *)

typedef T0 = [x,y:nat] T (x, y)
extern
fun theMemoTable_get0
  {x,y:nat} (x: int x, y: int y): Option (T0) = "theMemoTable_get"
extern
fun theMemoTable_set0
  {x,y:nat} (x: int x, y: int y, z: T0): void = "theMemoTable_set"

#define NX 100
#define NY 100
val theMemoTable = matrix_make_elt<Option(T0)> (NX, NY, None)

implement theMemoTable_get0 (x, y) =
  if x < NX then
    if y < NY then theMemoTable[x,NY,y] else None
  else None
// end of [theMemoTable_get0]

implement theMemoTable_set0 (x, y, res) =
  if x < NX then
    if y < NY then theMemoTable[x,NY,y] := Some (res) else ()
  else ()
// end of [theMemoTable_set0]

(* ****** ****** *)

implement
main () = () where {
(*
  #define N 10
  val (_pf | z) = f1 (N, N)
  val () = assert_errmsg (z = 184756, #LOCATION)
  val () = (printf ("f (%i, %i) = ", @(N, N)); print z; print_newline ())
*)
  #define N 20
  val (_pf | z) = f2 (N, N, mfun)
//
extern castfn of_ullint1 {i:nat} (x: ullint i):<> ullint
//
  val () = assert_errmsg (of_ullint1(z) = 137846528820ULL, #LOCATION)
  val () = (printf ("f (%i, %i) = ", @(N, N)); print z; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem15-hwxi2.dats] *)
