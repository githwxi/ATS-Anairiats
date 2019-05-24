//
// ProjectEuler: Problem 38
// Finding the largest 1-9 pandigital number that can be formed by multiplying
// a fixed number bb 1, 2, ..., n (for some n >= 2)
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"

(* ****** ****** *)

staload "libc/SATS/stdlib.sats"

(* ****** ****** *)

fun permPrev {n:nat} {l:addr}
  (pf: !array_v (int, n, l) | p: ptr l, n: size_t n): int =
  if n >= 2 then let
    val p2 = p+sizeof<int>
    prval (pf1, pf2) = array_v_uncons {int} (pf)
    val res = permPrev (pf2 | p2, n-1)
  in
    case+ 0 of
    | _ when res > 0 => let
        prval () = pf := array_v_cons {int} (pf1, pf2) in res
      end // end of [_ when ...]
    | _ (* res = 0 *) => let
        val x0 = !p
        fun loop {i:pos | i <= n} {l2:addr} .<n-i>. (
            pf2: !array_v (int, n-1, l2)
          | p2: ptr l2, x1: int, i1: sizeLt n, i: size_t i
          ) :<cloref> sizeLt n =
          if i < n then let
            val x = p2->[i-1]
          in
            if x < x0 then
              if (i1 > 0) then
                if (x > x1) then loop (pf2 | p2, x, i, i+1) else loop (pf2 | p2, x1, i1, i+1)
              else loop (pf2 | p2, x, i, i+1)
            else loop (pf2 | p2, x1, i1, i+1)
          end else i1
        val _0 = size1_of_int1 (0)
        val _1 = size1_of_int1 (1)
        val i1 = loop (pf2 | p2, ~1(*arb*), _0, _1)
        val () = if (i1 > 0) then let
          val () = !p := p2->[i1-1]; val () = p2->[i1-1] := x0
          val () = qsort {int} (!p2, n-1, sizeof<int>, lam (x1, x2) => compare (x2, x1))
        in
          // nothing
        end // end of [val]
        prval () = pf := array_v_cons {int} (pf1, pf2)
      in
        if (i1 > 0) then 1(*found*) else 0(*notfound*)
      end // end of [_]
    // end of [case+]
  end else 0(*notfound*)
// end of [permPrev]

(* ****** ****** *)

val DA: array (int, 9) =
  array_make_arrpsz{int}($arrpsz(9,8,7,6,5,4,3,2,1))
// end of [val]

fun DA_prev (): int = let
  val (vbox pf | p) = array_get_view_ptr (DA)
in
  $effmask_ref (permPrev (pf | p, 9))
end // end of [DA_prev]

fun DA_get
  {i,j:nat | i <= j; j <= 9}
  (i: int i, j: int j): int =
  if i < j then 10 * DA_get (i, j-1) + DA[j-1] else 0
// end of [DA_get]

(* ****** ****** *)

fun log10 (x: int): Nat =
  if x > 0 then 1 + log10 (x / 10) else 0
// end of [log10]

(* ****** ****** *)

fun test (): bool = let
  fun loop {i,j:nat | i <= 4; j <= 9}
    (i: int i, seed: int, j: int j, n: int): bool =
    if j <= 8 then let
      val x = n * seed
      val dj = log10 (x)
      stavar j1: int
      val j1: int j1 = (j + dj)
      val t = (
        if j1 <= 9 then let
          val res = DA_get (j, j1) = x in bool1_of_bool res
        end else false
      ) : [b:bool | (b && j1 <= 9) || ~b] bool (b)
    in
      if t then
        loop (i, seed, j1, n+1)
      else (
        if i < 4 then let
          val i1 = i+1 in loop (i1, DA_get (0, i1), i1, 2)
        end else false
      ) // end of [if]
    end else true
  // end of [loop]
in
  loop (1, DA_get (0, 1), 1, 2)
end // end of [test]

(* ****** ****** *)

implement
main () = () where {
  var ans: int = 0
  val () = while (true) let
    val () = if test () then
      let val () = ans := DA_get (0, 9) in break end
    // end of [val]
    val () = if DA_prev () = 0 then break
  in
    // nothing
  end // end of [val]
  val () = assert_errmsg (ans = 932718654, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem38-hwxi.dats] *)
