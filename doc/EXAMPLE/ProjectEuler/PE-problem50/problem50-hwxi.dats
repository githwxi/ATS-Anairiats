//
// ProjectEuler: Problem 50
// Finding the prime < 1M that can be written as the sum of longest
// consecutive sequence of primes
//

(* ****** ****** *)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: August, 2010
//

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/array.dats"
staload _(*anon*) = "prelude/DATS/list.dats"
staload _(*anon*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

#define N 1000000
val theArray = array_make_elt<int> (N, 1)
val () = theArray[0] := 0
val () = theArray[1] := 0
val () = sieve (2) where {
  fun remove {mp,p:nat}
    (mp: int mp, p: int p): void =
    if mp < N then let
      val () = theArray[mp] := 0 in remove (mp+p, p)
    end else ()
  // end of [remove]
  fun sieve {p:nat} .<N nsub p,0>.
    (p: int p): void =
    if p < N then let
      val () = remove (2*p, p) in sieve1 (p+1)
    end else ()
  // end of [sieve]
  and sieve1 {p1:nat} .<N nsub p1,1>.
    (p1: int p1): void =
    if p1 < N then
      (if theArray[p1] = 0 then sieve1 (p1+1) else sieve (p1))
    else ()
  // end of [sieve1]
} // end of [val]

(* ****** ****** *)

fun isPrime (n: natLt N): bool = theArray[n] = 1

(* ****** ****** *)

val thePrimes
  : List (Nat) = res where {
  fun loop {n:nat} .<N nsub n>.
    (n: int n, res: List_vt (Nat)): List_vt Nat =
    if n < N then
      if isPrime (n) then loop (n+1, list_vt_cons (n, res)) else loop (n+1, res)
    else res // end of [if]
  val res = loop (0, list_vt_nil)
  val res = list_vt_reverse (res)
  val res = list_of_list_vt (res)  
} // end of [va]

(*
val () = list_foreach_fun<int> (thePrimes, lam (p) =<1> printf ("%i\n", @(p)))
*)

(* ****** ****** *)

fun search_aux
  (ps: List (Nat), psum: Nat, n: Nat, pres: int, nres: int): @(int, int) = let
  // nothing
in
  case+ ps of
  | list_cons (p, ps) => let
      val psum1 = psum + p; val n1 = n + 1
    in
      if psum1 < N then
        if isPrime (psum1) then search_aux (ps, psum1, n1, psum1, n1)
        else search_aux (ps, psum1, n1, pres, nres)
      else @(pres, nres)
    end // end of [list_cons]
  | list_nil () => @(pres, nres)
end // end of [search_aux]

fun search
  (ps: List (Nat), pres: int, cnt: int): int =
  case+ ps of
  | list_cons (p, ps) => let
      val (pres1, cnt1) = search_aux (ps, p, 1, p, 1)
    in
      if cnt1 > cnt then search (ps, pres1, cnt1) else search (ps, pres, cnt)
    end // end of [list_cons]
  | list_nil () => let
      val () = (print "search: cnt = "; print cnt; print_newline ())
      val () = (print "search: pres = "; print pres; print_newline ())
    in
      pres
    end // end of [list_nil]
// end of [search]

(* ****** ****** *)

implement main () = () where {
  val ans = search (thePrimes, 0, 0)
  val () = assert_errmsg (ans = 997651, #LOCATION)
  val () = (print "ans = "; print ans; print_newline ())
} // end of [main]

(* ****** ****** *)

(* end of [problem50-hwxi.dats] *)
