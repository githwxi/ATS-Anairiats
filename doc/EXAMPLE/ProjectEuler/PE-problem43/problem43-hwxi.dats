//
// ProjectEuler: Problem 43
// Finding the largest pandigital prime
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

fun permNext {n:nat} {l:addr}
  (pf: !array_v (int, n, l) | p: ptr l, n: size_t n): int =
  if n >= 2 then let
    val p2 = p+sizeof<int>
    prval (pf1, pf2) = array_v_uncons {int} (pf)
    val res = permNext (pf2 | p2, n-1)
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
            if x > x0 then
              if (i1 > 0) then
                if (x < x1) then loop (pf2 | p2, x, i, i+1) else loop (pf2 | p2, x1, i1, i+1)
              else loop (pf2 | p2, x, i, i+1)
            else loop (pf2 | p2, x1, i1, i+1)
          end else i1
        val _0 = size1_of_int1 (0)
        val _1 = size1_of_int1 (1)
        val i1 = loop (pf2 | p2, ~1(*arb*), _0, _1)
        val () = if (i1 > 0) then let
          val () = !p := p2->[i1-1]; val () = p2->[i1-1] := x0
          val () = qsort {int} (!p2, n-1, sizeof<int>, lam (x1, x2) => compare (x1, x2))
        in
          // nothing
        end // end of [val]
        prval () = pf := array_v_cons {int} (pf1, pf2)
      in
        if (i1 > 0) then 1(*found*) else 0(*notfound*)
      end // end of [_]
    // end of [case+]
  end else 0(*notfound*)
// end of [permNext]

(* ****** ****** *)

val DA: array (int, 10) =
  array_make_arrpsz{int}($arrpsz(0,1,2,3,4,5,6,7,8,9))
// end of [val]

fun DA_next (): int = let
  val (vbox pf | p) = array_get_view_ptr (DA)
in
  $effmask_ref (permNext (pf | p, 10))
end // end of [DA_next]

(* ****** ****** *)

fun DA_get (): ullint = let
  fun loop {i:nat | i <= 10}
    (res: ullint, i: int i): ullint =
    if i < 10 then loop (10ULL * res + (ullint_of)DA[i], i+1) else res
  // end of [loop]
in
  loop (0ULL, 0)
end // end of [DA_get]

(* ****** ****** *)

exception Failed

fun testExn (): void = let
//
  val _0 = 1
  val d = 100 * DA[_0] + 10 * DA[_0+1] + DA[_0+2]
  val () = if d mod 2 <> 0 then $raise Failed
//
  val _0 = 2
  val d = 100 * DA[_0] + 10 * DA[_0+1] + DA[_0+2]
  val () = if d mod 3 <> 0 then $raise Failed
//
  val _0 = 3
  val d = 100 * DA[_0] + 10 * DA[_0+1] + DA[_0+2]
  val () = if d mod 5 <> 0 then $raise Failed
//
  val _0 = 4
  val d = 100 * DA[_0] + 10 * DA[_0+1] + DA[_0+2]
  val () = if d mod 7 <> 0 then $raise Failed
//
  val _0 = 5
  val d = 100 * DA[_0] + 10 * DA[_0+1] + DA[_0+2]
  val () = if d mod 11 <> 0 then $raise Failed
//
  val _0 = 6
  val d = 100 * DA[_0] + 10 * DA[_0+1] + DA[_0+2]
  val () = if d mod 13 <> 0 then $raise Failed
//
  val _0 = 7
  val d = 100 * DA[_0] + 10 * DA[_0+1] + DA[_0+2]
  val () = if d mod 17 <> 0 then $raise Failed
//
in
  // nothing
end // end of [test]

fun test (): bool = try testExn (); true with ~Failed () => false

(* ****** ****** *)

implement
main () = () where {
  var sum: ullint = 0ULL
  val () = while (true) let
    val () = if
      test() then let
      val n = DA_get ()
(*
      val () = (print "n = "; print n; print_newline ())
*)
    in
      sum := sum + n
    end // end of [if]
    val found = DA_next ()
  in
    if found = 0 then break
  end // end of [val]
  val ans = sum
  val () = assert_errmsg (ans = 16695334890ULL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem43-hwxi.dats] *)
