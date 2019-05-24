//
// ProjectEuler: Problem 49
// Finding 3 4-digit permutative primes that form an arithmetic sequence
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)

staload "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "libc/SATS/stdlib.sats"

(* ****** ****** *)

fun permNext {n:nat} {l:addr}
  (pf: !array_v (uint, n, l) | p: ptr l, n: size_t n): int = let
  typedef T = uint
in
  if n >= 2 then let
    val p2 = p+sizeof<T>
    prval (pf1, pf2) = array_v_uncons {T} (pf)
    val res = permNext (pf2 | p2, n-1)
  in
    case+ 0 of
    | _ when res > 0 => let
        prval () = pf := array_v_cons {T} (pf1, pf2) in res
      end // end of [_ when ...]
    | _ (* res = 0 *) => let
        val x0 = !p
        fun loop {i:pos | i <= n} {l2:addr} .<n-i>. (
            pf2: !array_v (T, n-1, l2) | p2: ptr l2, x1: T, i1: sizeLt n, i: size_t i
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
        val i1 = loop (pf2 | p2, 0U(*arb*), _0, _1)
        val () = if (i1 > 0) then let
          val () = !p := p2->[i1-1]; val () = p2->[i1-1] := x0
          val () = qsort {T} (!p2, n-1, sizeof<T>, lam (x1, x2) => compare (x1, x2))
        in
          // nothing
        end // end of [val]
        prval () = pf := array_v_cons {T} (pf1, pf2)
      in
        if (i1 > 0) then 1(*found*) else 0(*notfound*)
      end // end of [_]
    // end of [case+]
  end else 0(*notfound*)
end // end of [permNext]

(* ****** ****** *)

fun log10 (n: uint): Nat =
  if n > 0U then 1 + log10 (n/10U) else 0
// end of [log10]

(* ****** ****** *)
//
macdef size1 (x) = size1_of_int1 ,(x)
//
fun getPermNext
  (x: uint, flag: &int? >> int): uint = let
  typedef T = uint
  val [n:int] ndigit = log10 (x)
  var !p_arr with pf_arr = @[uint][ndigit]()
  val (pfmul | ofs) =
    mul2_size1_size1 ((size1)ndigit, sizeof<T>)
  // end of [val]
  val () = loop (pfmul, pf_arr | p_arr+ofs, ndigit, x) where {
    fun loop {n:nat} {l:addr} {ofs: int} (
        pfmul: MUL (n, sizeof T, ofs)
      , pf: !array_v (T?, n, l) >> array_v (T, n, l) | p: ptr (l+ofs), n: int n, x: T
      ) : void = let
      val n1 = n - 1
    in
      if n1 >= 0 then let
        prval (pf1, pf2) = array_v_unextend {T?} (pfmul, pf)
        val p1 = p - sizeof<T>
        val () = !p1 := x mod 10U
        prval pfmul = mul_add_const {~1} (pfmul)
        val () = loop (pfmul, pf1 | p1, n-1, x/10U)
        prval () = pf := array_v_extend {T} (pfmul, pf1, pf2)
      in
        // nothing
      end else let
        prval () = array_v_unnil (pf)
        prval () = pf := array_v_nil {T} ()
      in
        // nothing
      end // end of [if]
    end // end of [loop]
  } // end of [val]
  val () = flag :=
    permNext (pf_arr | p_arr, (size1)ndigit)
  val res = loop (pf_arr | p_arr, ndigit, 0U) where {
    fun loop {n:nat} {l:addr}
      (pf: !array_v (T, n, l) | p: ptr l, n: int n, res: T): T =
      if n > 0 then let
        prval (pf1, pf2) = array_v_uncons {T} (pf)
        val res = 10U * res + !p
        val res = loop (pf2 | p+sizeof<T>, n-1, res)
        prval () = pf := array_v_cons {T} (pf1, pf2)
      in
        res
      end else res // end of [if]
    // end of [loop]
  } // end of [val]
in
  res
end // end of [getPermNext]

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

fn isprime
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

fn isprime (n: uint): bool = let
  val n = int1_of_uint1 (uint1_of_uint (n))
in
  if n >= 2 then isprime (n) else false
end // end of [isprime]

(* ****** ****** *)

val theAnswer = ref_make_elt<ullint> (0ULL)

(* ****** ****** *)

fun test2 (
  x: uint, x1: uint, x2: uint
) : bool = let
  var flag: int
  val x2 = getPermNext (x2, flag)
in
  if flag > 0 then let
    val sgn = compare (x2+x, x1+x1)
  in
    if sgn < 0 then test2 (x, x1, x2) else (
      if (sgn = 0) then let
        val ans = isprime (x2)
(*
        val () = if ans then printf ("%u%u%u\n", @(x,x1,x2))
*)
        val () = !theAnswer := (ullint_of)x
        val () = !theAnswer := !theAnswer * 10000ULL + (ullint_of)x1
        val () = !theAnswer := !theAnswer * 10000ULL + (ullint_of)x2
      in
        ans
      end else false
    ) // end of [if]
  end else false
end // end of [test2]

fun test1 (
  x: uint, x1: uint
) : bool = let
(*
  val () = (print "test1: x = "; print x; print_newline ())
  val () = (print "test1: x1 = "; print x1; print_newline ())
*)
  var flag: int
  val x1 = getPermNext (x1, flag)
in
  if flag > 0 then (
    if isprime x1 then
      (if test2 (x, x1, x1) then true else test1 (x, x1))
    else test1 (x, x1)
  ) else false
end // end of [test1]

fun test
  (x: uint): bool =
  if isprime x then test1 (x, x) else false
// end of [test]

val () = assert_errmsg (test (1487U), #LOCATION)

(* ****** ****** *)

implement
main () = () where {
  var x: uint
  val () = for
    (x := 1000U; x < 10000U; x := x+1U) (if test (x) then (if x <> 1487U then break))
  // end of [val]
  val ans = !theAnswer
  val () = assert_errmsg (ans = 296962999629ULL, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem49-hwxi.dats] *)
