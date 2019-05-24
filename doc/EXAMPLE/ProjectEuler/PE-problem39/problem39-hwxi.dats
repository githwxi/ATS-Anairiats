//
// ProjectEuler: Problem 39
// Finding the number p <= 1000 such that the equation a+b+c=p
// has the maximal number of solutions, where a,b and c are the
// sides of a right triangle
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)
//
// HX: 
// Assume p1 <= q1 and p2 <= q2 and the following two sets are the same:
// {p1^2+q1^2,2*p1*q1,p1^2-q1^2}
// {p2^2+q2^2,2*p2*q2,p2^2-q2^2}
// Then it is straightforward to show p1=p2 and q1=q2:
// clearly p1^2+q1^2=p2^2+q2^2
// 1) if 2*p1*q1 = 2*p2*q2, then we are done.
// 2) if 2*p1*q1 = p2^2-q2^2, then (p1+q1)^2 = 2*p2^2, which is a contradiction
//
// HX: the above proof is _not_ used in the following implementation
//
(* ****** ****** *)

fun isqrt (x: int): int = int_of (sqrt (x - 0.5))

(* ****** ****** *)

fun isprime
  (x: int): bool = let
  val xq = isqrt (x)
  fun loop (x: int, i: int):<cloref1> bool =
    if i <= xq then
      if x mod i = 0 then false else loop (x, i+1)
    else true
in
  if x >= 2 then loop (x, 2) else false
end // end of [isprime]

(* ****** ****** *)

viewtypedef intlst = List_vt (int)

fun eval1 (x: int): intlst = let
  val xq = isqrt (x)
(*
  val () = (print "eval1: x = "; print x; print_newline ())
  val () = (print "eval1: xq = "; print xq; print_newline ())
*)
  fun loop (i: int, res: &intlst):<cloref1> void =
    if i <= xq then (
      if x mod i = 0 then let
        val j = x / i
        val ji = j - i
        val () = if ji < i andalso gcd (i, ji) = 1 then
          let val a = i*i + ji*ji in (res := list_vt_cons (a, res)) end
        // end of [val]
      in
        loop (i+1, res)
      end else loop (i+1, res) // end of [if]
    ) // end of [if]
  var res: intlst = list_vt_nil ()
  val () = loop (2, res)
in
  res
end // end of [eval1]

(* ****** ****** *)

fun insert (xs: intlst, x0: int): intlst =
  case+ xs of
  | list_vt_nil () => (fold@ xs; list_vt_cons (x0, xs))
  | list_vt_cons (x, !p_xs1) =>
      if x0 < x then (fold@ xs; list_vt_cons (x0, xs))
      else if x0 > x then (!p_xs1 := insert (!p_xs1, x0); fold@ xs; xs)
      else (fold@ xs; xs)
    // end of [list_vt_cons]
// end of [insert]

fun merge (res: intlst, k: int, xs: intlst): intlst =
  case+ xs of
  | ~list_vt_cons (x, xs) => let
      val res = insert (res, k * x) in merge (res, k, xs)
    end // end of [list_vt_cons]
  | ~list_vt_nil () => res
// end of [merge]

fun eval2 (x: int): int = let
  fun loop (x2: int, k: int, res: intlst): intlst =
    if k+k <= x2 then
      if x2 mod k = 0 then let
        val res1 = eval1 (x2 / k)
        val res = merge (res, k, res1) in loop (x2, k+1, res)
      end else loop (x2, k+1, res)
    else res
in
  if x mod 2 = 0 then let
    val res = loop (x/2, 1, list_vt_nil)
    val n = list_vt_length (res); val () = list_vt_free (res)
  in
    n
  end else 0
end // end of [eval2]

(* ****** ****** *)

val () = assert_errmsg (eval2 (120) = 3, #LOCATION)

(* ****** ****** *)

implement
main () = () where {
  #define N 1000
  var max: int = 0
  var maxres: int = 0
  var x: int
  val () = for
    (x := 2; x <= N; x := x+1) let
    val res = eval2 (x)
    val () = if res > maxres then (max := x; maxres := res)
  in
    // nothing
  end // end of [val]
  val ans = max
  val () = assert_errmsg (ans = 840, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem39-hwxi.dats] *)
