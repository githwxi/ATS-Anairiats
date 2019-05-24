//
// ProjectEuler: Problem 32
// Finding all the products whose multiplicand/multiplier/product identity
// can be written as a 1 thru 9 pandigit
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

typedef intlst = List (int)

val theLst = ref<intlst> (list_nil) // it is sorted

fun theLst_add (x0: int): void = let
  fun aux (xs: intlst):<cloref1> intlst =
    case+ xs of
    | list_nil () => list_cons (x0, list_nil)
    | list_cons (x, xs1) =>
        if x0 < x then list_cons (x0, xs) else if x0 > x then list_cons (x, aux (xs1)) else xs
      // end of [list_cons]
in
  !theLst := aux (!theLst)
end // end of [val]

fun theLst_sum (): int = loop (!theLst, 0) where {
  fun loop (xs: intlst, res: int): int =
    case+ xs of
    | list_cons (x, xs) => loop (xs, res+x) | list_nil () => res
  // end of [loop]
} // end of [theLst_sum]

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

val DA: array (int, 9) =
  array_make_arrpsz{int}($arrpsz(1,2,3,4,5,6,7,8,9))
// end of [val]

fun DA_next (): int = let
  val (vbox pf | p) = array_get_view_ptr (DA)
in
  $effmask_ref (permNext (pf | p, 9))
end // end of [DA_next]

fun DA_get
  {i,j:nat | i <= j; j <= 9}
  (i: int i, j: int j): int =
  if i < j then 10 * DA_get (i, j-1) + DA[j-1] else 0
// end of [DA_get]

(* ****** ****** *)

fun eval2 
  {i,j:nat | i < j; j <= 9} (i: int i, j: int j): void =
  if j <= 8 then let
    val x1 = DA_get (0, i)
    val x2 = DA_get (i, j)
    val x3 = DA_get (j, 9)
    val () = if x1 * x2 = x3 then theLst_add (x3)
  in
    eval2 (i, j+1)
  end // end of [if]
// end of [eval2]

fun eval1 {i:nat | i <= 5} (i: int i): void =
  if i < 5 then let
    val () = eval2 (i, i+1) in eval1 (i+1)
  end // end of [if]
// end of [eval1]

(* ****** ****** *)

implement
main () = () where {
  val () = while (true) let
    val () = eval1 (1)
    val found = DA_next ()
  in
    if found = 0 then break
  end // end of [val]
  val ans = theLst_sum ()
  val () = assert_errmsg (ans = 45228, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem32-hwxi.dats] *)
