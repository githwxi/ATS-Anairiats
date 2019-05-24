//
// ProjectEuler: Problem 125
// Finding palindrome numbers that can be represented as the sum of
// two or more consecutive squares
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload "prelude/DATS/list.dats"
staload "prelude/DATS/reference.dats"

(* ****** ****** *)

fun ispalin
  (x: int): bool = let
  fun rev (x: int, rx: int): int =
    if x > 0 then let
      val r = x mod 10 in rev (x / 10, 10*rx + r)
    end else rx
  // end of [res]
in
  x = rev (x, 0)
end // end of [ispalin]

(* ****** ****** *)

macdef f (n) = let
  val n = ,(n) in n * (n+1) * (2*n+1) / 6
end // end of [f]

(* ****** ****** *)

typedef intlst = List int
val theList: ref (intlst) = ref<intlst> (list_nil)

(* ****** ****** *)

fun insert (x0: int, xs: intlst): intlst =
  case+ xs of
  | list_cons (x, xs1) =>
      if x0 < x then list_cons (x0, xs)
      else if x0 > x then list_cons (x, insert (x0, xs1))
      else xs
   | list_nil () => list_cons (x0, xs)
// end of [insert]

(* ****** ****** *)

fun theList_add (x0: int): void =
  !theList := insert (x0, !theList)
// end of [theList_add]

fun theList_sum
  (): llint = loop (!theList, 0LL) where {
  fun loop (xs: intlst, res: llint): llint = 
    case+ xs of
    | list_cons (x, xs) => loop (xs, res + (llint_of)x)
    | list_nil () => res
  // end of [loop]
} // end of [theList_sum]

(* ****** ****** *)

fun eval (
    n: int, N2: double
  ) : void = let
  val nf = double_of (n)
  val sum1 = f (nf)
  fun loop
    (k: int):<cloref1> void =
    if k+1 < n then let
      val kf = double_of (k)
      val sum2 = f (kf)
      val diff = sum1 - sum2
    in
      if diff >= N2
        then loop (k+1)
      else let
        val diff = int_of (diff)
        val () = if ispalin (diff) then theList_add (diff)
      in
        loop (k+1)
      end // end of [if]
    end // end of [if]
in
  loop (0)
end // end of [eval]

(*
//
// HX: this is used for testing
//
val () = let
  var n: int // unintialized
  val () = !theList := list_nil
  val () = for (n := 1; n < 32; n := n+1) eval (n, 1000.0)
  val len = list_length (!theList)
//  val () = (print "len = "; print len; print_newline ())
  val () = assert_errmsg (len = 11, #LOCATION)
  val sum = theList_sum ()
//  val () = (print "sum = "; print sum; print_newline ())
  val () = assert_errmsg (sum = 4164LL, #LOCATION)
in
  // nothing
end // end of [val]
*)

(* ****** ****** *)

staload "libc/SATS/math.sats"

implement main () = () where {
  #define _100M 100000000.0 // 10^8
  val N = sqrt (_100M + 0.5)
  val N = int_of (N)
  var n: int // unintialized
  val () = !theList := list_nil
  val () = for (n := 1; n < N; n := n+1) eval (n, _100M)
  val ans = theList_sum ()
  val () = assert_errmsg (ans = 2906969179LL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem125-hwxi.dats] *)
