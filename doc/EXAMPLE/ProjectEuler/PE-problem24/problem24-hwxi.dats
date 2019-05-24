//
// ProjectEuler: Problem 24
// Finding the 1000000th permutation of 0123456789
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

implement
main () = () where {
  val N = 1000000 // 1M
  var i: int // uninitialized
  val () = for (i := 1; i < N; i := i+1) let val _ = DA_next () in (*none*) end
  val ans = DA_get ()
  val () = assert_errmsg (ans = 2783915460ULL, #LOCATION)
  val () = printf ("ans = %10.10llu\n", @(ans))
} // end of [main]

(* ****** ****** *)

(* end of [problem24-hwxi.dats] *)
