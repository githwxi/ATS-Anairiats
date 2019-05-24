//
// ProjectEuler: Problem 41
// Finding the largest pandigital prime
//

(* ****** ****** *)
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
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

fun isqrt
  (x: uint): uint =
  if x >= 2U then let
    val x4 = x / 4U
    val r2 = isqrt (x4)
    val r = r2 + r2
    val r_1 = r + 1U
  in
    if r_1 * r_1 > x then r else r_1
  end else x 
// end of [isqrt]

(* ****** ****** *)

fun isprime
  {n:int | n >= 2}
  (n: int n): bool = let
  val u = uint_of_int (n)
  val r = isqrt (u)
(*
  val () = (print "u = "; print u; print_newline ())
  val () = (print "r = "; print r; print_newline ())
*)
  fun loop (p: uint):<cloref1> bool =
    if p <= r then
      (if (u mod p > 0U) then loop (p+1U) else false)
    else true
  // end of [loop]
in
  loop (2U)
end // end of [isprime]

(* ****** ****** *)
//
// clearly, any 8-digit or 9-digit pandigit number is a multiple of 3.
//
(* ****** ****** *)

val A7: array (int, 7) =
  array_make_arrpsz{int}($arrpsz(7, 6, 5, 4, 3, 2, 1))
// end of [val]

fun A7_get (): int = let
  fun loop {i:nat | i <= 7}
    (res: int, i: int i): int =
    if i < 7 then loop (10 * res + A7[i], i+1) else res
  // end of [loop]
in
  loop (0, 0)
end // end of [A7_get]

fun A7_prev (): int = let
  val (vbox pf | p) = array_get_view_ptr (A7)
in
  $effmask_ref (permPrev (pf | p, 7))
end // end of [A7_prev]

(* ****** ****** *)

implement
main () = () where {
  var ans: int = 0
//
  val () = while (true) let
    val n = A7_get ()
    val n = int1_of_int (n)
    val () = assert (n >= 2)
    val test = isprime (n)
  in
    if (test) then (ans := n; break)
    else let
      val found = A7_prev () in if found = 0 then break
    end // end of [if]
  end // end of [val]
//
  val () = assert_errmsg (ans = 7652413, #LOCATION)
//
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem41-hwxi.dats] *)
